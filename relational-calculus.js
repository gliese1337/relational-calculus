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
        if (!(other instanceof AlgebraNode)) {
            other = new Relation(other);
        }

        return new Join(this, other, links);
    }

    theta(other, rels) {
        if (!(other instanceof AlgebraNode)) {
            other = new Relation(other);
        }

        return new Theta(this, other, rels);
    }

    semijoin(other, rels) {
        if (!(other instanceof AlgebraNode)) {
            other = new Relation(other);
        }

        return new SemiJoin(this, other, rels);
    }

    antijoin(other, rels) {
        if (!(other instanceof AlgebraNode)) {
            other = new Relation(other);
        }

        return new AntiJoin(this, other, rels);
    }

    divide(other, scol, ocol = scol) {
        if (!(other instanceof AlgebraNode)) {
            other = new Relation(other);
        }

        return new Division(this, other, scol, ocol);
    }
    
    union(other) {
        if (!(other instanceof AlgebraNode)) {
            other = new Relation(other);
        }

        return new Union(this, other);
    }
} 

class Projection extends AlgebraNode {
    constructor(node, columns) {
        this.rows = node.rows.map((row) => {
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
        columns = new Set(columns);
        this.rows = node.rows.map((row) => {
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
        this.rows = node.rows.map((row) => {
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
        this.rows = node.rows.filter((row) =>
            criteria.every((crit) => 
                (crit.hasOwnProperty('value') && row[crit.col] === crit.value) ||
                (typeof crit.predicate !== 'function' || crit.predicate(row[crit.col]))
            )
        );
    }
}

class Join extends AlgebraNode {
    constructor({ rows: self }, { rows: other }, links) {
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

        this.rows = nrows;
    }
}

class Theta extends AlgebraNode {
    constructor({ rows: self }, { rows: other }, rels) {
        const nrows = [];

        for (const srow of self) {
            for (const orow of other) {
                const match = rels.every(({ self, other, predicate }) =>
                    predicate(srow[self], orow[other]));
                if (!match) continue;
                nrows.push({ ...orow, ...srow });
            }
        }

        this.rows = nrows;
    }
}

class SemiJoin extends AlgebraNode {
    constructor({ rows: self }, { rows: other }, rels) {
        this.rows = self.filter((srow) => semijoinMatchExists(srow, other, rels));
    }
}

class AntiJoin extends AlgebraNode {
    constructor({ rows: self }, { rows: other }, rels) {
        this.rows = self.filter((srow) => !semijoinMatchExists(srow, other, rels));
    }
}

class Division extends AlgebraNode {
    constructor({ rows: self }, { rows: other }, scol, ocol) {
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

        this.rows = nrows;
    }
}

class Union extends AlgebraNode {
    constructor(self, other) {
        this.rows = [ ...self.rows, ...other.rows ];
    }
}

export class Relation extends AlgebraNode {
    constructor(...rows) {
        if(rows[0] instanceof AlgebraNode) {
            return rows[0];
        }

        this.rows = rows.flat();
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
}
