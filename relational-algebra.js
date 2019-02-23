function semijoinMatchExists(srow, other, rels) {
    return other.some((orow) =>
        rels.every(({ self, other, predicate }) =>
            typeof predicate === 'function' ?
                predicate(srow[self], orow[other]) :
                srow[self] === orow[other]
        )
    );
}

function symmetricEqual(iobj, jobj) {
    if (iobj === jobj) return true;
    const jkeys = new Set(Object.keys(jobj));
    for (const k of Object.keys(iobj)) {
        if (!symmetricEqual(iobj[k], jobj[k])) return false;
        jkeys.delete(k);
    }

    for (const k of jkeys) {
        if (!symmetricEqual(iobj[k], jobj[k])) return false;
    }

    return true;
}

function getFieldsExcept(obj, field, cache) {
    if(cache.has(obj)) return cache.get(obj);

    const fields = new Set(Object.keys(obj));
    fields.delete(field);
    cache.set(obj, fields);

    return fields;
}

function symmetricEqualExcept(iobj, jobj, field, cache) {
    if (iobj === jobj) return true;
    const ifields = getFieldsExcept(iobj, field, cache);
    const jfields = new Set(getFieldsExcept(jobj, field, cache));
    for (const k of ifields) {
        if (!symmetricEqual(iobj[k], jobj[k])) return false;
        jfields.delete(k);
    }

    for (const k of jfields) {
        if (!symmetricEqual(iobj[k], jobj[k])) return false;
    }
}

function extract(obj, fields) {
    return fields.map((k) => {
        const v = obj[k];
        delete obj[k];

        return v;
    });
}

function toRelation(t) {
    return t instanceof AlgebraNode ? t : new Relation(t);
}

class AlgebraNode {

    project(...columns) {
        return new Projection(this, columns.flat());
    }

    drop(...columns) {
        return new AntiProjection(this, columns.flat());
    }

    rename(changes) {
        return new Rename(this, changes);
    }

    select(...criteria) {
        return new Select(this, criteria.flat());
    }

    join(other, links) {
        return new Join(this, toRelation(other), links);
    }

    theta(other, rels) {
        return new Theta(this, toRelation(other), rels);
    }

    semijoin(other, rels) {
        return new SemiJoin(this, toRelation(other), rels);
    }

    antijoin(other, rels) {
        return new AntiJoin(this, toRelation(other), rels);
    }

    divide(other, scol, ocol = scol) {
        return new Division(this, toRelation(other), scol, ocol);
    }
    
    union(other) {
        return new Union(this, toRelation(other));
    }

    unique() {
        return new Unique(this);
    }

    get rows() {
        if (this._rows === null) this._calcrows();

        return this._rows;
    }

    get relation() {
        if (!this._table) {
            this._table = new Relation(this.rows);
        }

        return this._table;
    }

    get resolved() {
        return this._rows instanceof Array;
    }
} 

class Projection extends AlgebraNode {
    constructor(node, columns) {
        this.node = node;
        this.columns = columns;
        this._rows = null;
    }

    _calcrows() {
        const [ node, columns ] = extract(this, [ 'node', 'columns' ]);
        this._rows = node.rows.map((row) => {
            const nr = {};
            for (const c of columns) {
                nr[c] = row[c];
            }

            return nr;
        });
    }
}

class AntiProjection extends AlgebraNode {
    constructor(node, columns) {
        this.node = node;
        this.columns = new Set(columns);
        this._rows = null;
    }

    _calcrows() {
        const [ node, columns ] = extract(this, [ 'node', 'columns' ]);
        this._rows = node.rows.map((row) => {
            const nr = {};
            for (const c of Object.keys(row)) {
                if (columns.has(c)) continue;
                nr[c] = row[c];
            }

            return nr;
        });
    }
}

class Rename extends AlgebraNode {
    constructor(node, changes) {
        this.node = node;
        this.changes = changes;
        this._rows = null;
    }

    _calcrows() {
        const [ node, changes ] = extract(this, [ 'node', 'changes' ]);
        this._rows = node.rows.map((row) => {
            const nr = {};
            for (const k of Object.keys(row)) {
                const ckey = changes[k];
                const nkey = typeof ckey === 'string' ? ckey : k;
                nr[nkey] = row[k];
            }

            return nr;
        });
    }
}

class Select extends AlgebraNode {
    constructor(node, criteria) {
        this.node = node;
        this.criteria = criteria;
        this._rows = null;
    }

    _calcrows() {
        const [ node, criteria ] = extract(this, [ 'node', 'criteria' ]);
        this._rows = node.rows.filter((row) =>
            criteria.every((crit) => 
                (crit.hasOwnProperty('value') && row[crit.col] === crit.value) ||
                (typeof crit.predicate !== 'function' || crit.predicate(row[crit.col]))
            )
        );
    }
}

class Join extends AlgebraNode {
    constructor(snode, onode, links) {
        this.snode = snode;
        this.onode = onode;
        this.links = links;
        this._rows = null;
    }

    _calcrows() {
        const [ { rows: self }, { rows: other }, links ] =
            extract(this, [ 'snode', 'onode', 'links' ]);

        const sjcols = new Set();
        const ojcols = new Set();
        for (const { self, other } of links) {
            sjcols.add(self);
            ojcols.add(other);
        }

        for (const srow of self) {
            const skeys = Object.keys(srow).filter((k) => !sjcols.has(k));
            tloop: for (const orow of other) {
                const okeys = new Set(Object.keys(orow).filter((k) => !ojcols.has(k)));
                const matches = skeys
                    .filter((k) => okeys.has(k))
                    .map((k) => ({ self: k, other: k, as: k }));

                const nr = {};
                for (const { self, other, as } of [...links, ...matches]) {
                    const v = srow[self];
                    if (v !== orow[other]) {
                        continue tloop;
                    }
                    
                    nr[as] = v;
                }

                for (const k of skeys) {
                    nr[k] = srow[k];
                }

                for (const k of okeys) {
                    nr[k] = orow[k];
                }

                nrows.push(nr);
            }
        }

        this._rows = nrows;
    }
}

class Theta extends AlgebraNode {
    constructor(snode, onode, rels) {
        this.snode = snode;
        this.onode = onode;
        this.rels = rels;
        this._rows = null;
    }

    _calcrows() {
        const [ { rows: self }, { rows: other }, rels ] =
            extract(this, [ 'snode', 'onode', 'rels' ]);

        const nrows = [];
        for (const srow of self) {
            for (const orow of other) {
                const match = rels.every(({ self, other, predicate }) =>
                    predicate(srow[self], orow[other]));
                if (!match) continue;
                nrows.push({ ...orow, ...srow });
            }
        }

        this._rows = nrows;
    }
}

class SemiJoin extends AlgebraNode {
    constructor(snode, onode, rels) {
        this.snode = snode;
        this.onode = onode;
        this.rels = rels;
        this._rows = null;
    }

    _calcrows() {
        const [ { rows: self }, { rows: other }, rels ] =
            extract(this, [ 'snode', 'onode', 'rels' ]);
        
        this._rows = self.filter((srow) => semijoinMatchExists(srow, other, rels));
    }
}

class AntiJoin extends AlgebraNode {
    constructor(snode, onode, rels) {
        this.snode = snode;
        this.onode = onode;
        this.rels = rels;
        this._rows = null;
    }

    _calcrows() {
        const [ { rows: self }, { rows: other }, rels ] =
            extract(this, [ 'snode', 'onode', 'rels' ]);
        
        this._rows = self.filter((srow) => !semijoinMatchExists(srow, other, rels));
    }
}

class Division extends AlgebraNode {
    
    constructor(snode, onode, scol, ocol) {
        this.snode = snode;
        this.onode = onode;
        this.scol = scol;
        this.ocol = ocol;
        this._rows = null;
    }

    _calcrows() {
        const [ { rows: self }, { rows: other }, scol, ocol ] =
            extract(this, [ 'snode', 'onode', 'scol', 'ocol' ]);

        const values = new Set(other.map((orow) => orow[ocol]));
        const l = self.length;
        const used = new Set();
        const nrows = [];

        outer: for (let i = 0; i < l; i++) {
            if(used.has(i)) continue;
            const irow = self[i];
            const ivals = new Set(values);
            for (let j = i + 1; j < l; j++) {
                const jrow = self[j];
                if (symmetricEqualExcept(irow, jrow, scol)){
                    ivals.delete(jrow[scol]);
                    used.add(j);
                    
                    if(ivals.size === 0) {
                        const nr = { ...irow };
                        delete nr[scol];
                        nrows.push(nr);
                        continue outer;
                    }
                }
            }
        }

        this._rows = nrows;
    }
}

class Union extends AlgebraNode {
    constructor(snode, onode) {
        this.snode = snode;
        this.onode = onode;
        this._rows = null;
    }

    _calcrows() {
        const [ { rows: self }, { rows: other } ] = extract(this, [ 'snode', 'onode' ]);
        this._rows = [ ...self, ...other ];
    }
}

class Unique extends AlgebraNode {
    constructor(node) {
        this.node = node;
        this._rows = null;
    }

    _calcrows() {
        const nrows = [];
        const { rows } = this.node;
        const l = rows.length;
        this.node = null;

        for (let i = 0; i < l; i++) {
            const row = rows[i];
            if (!nrows.some((r) => symmetricEqual(r, row))){
                nrows.push(row);
            }
        }
        
        this._rows = nrows;
    }
}

export class Relation extends AlgebraNode {
    constructor(...rows) {
        if(rows[0] instanceof AlgebraNode) {
            return rows[0];
        }

        this._rows = rows.flat();
    }

    get relation() {
        return this;
    }

    static project(table, columns) {
        return new Projection(new Relation(table), columns);
    }

    static drop(table, columns) {
        return new AntiProjection(new Relation(table), columns);
    }

    static rename(table, changes) {
        return new Rename(new Relation(table), changes);
    }

    static select(table, criteria) {
        return new Select(new Relation(table), criteria);
    }

    static join(self, other, links = []) {
        return new Join(new Relation(self), new Relation(other), links);
    }

    static theta(self, other, rels) {
        return new Theta(new Relation(self), new Relation(other), rels);
    }

    static semijoin(self, other, rels) {
        return new SemiJoin(new Relation(self), new Relation(other), rels);
    }

    static antijoin(self, other, rels) {
        return new AntiJoin(new Relation(self), new Relation(other), rels);
    }

    static divide(self, other, scol, ocol = scol) {
        return new Divide(new Relation(self), new Relation(other), scol, ocol);
    }

    static union(self, other) {
        return new Union(new Relation(self), new Relation(other));
    }

    static unique(table) {
        return new Unique(new Relation(table));
    }
}
