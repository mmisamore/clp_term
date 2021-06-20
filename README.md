# Description

**clp(Term): Constraint Logic Programming for the Standard Ordering of Terms**

This module exposes the standard ordering on Prolog terms as an interval theory, thereby providing fully declarative
replacements for the predicates `@</2`, `@=</2`, `@>/2`, `@>=/2`. It is intended for use with SWI Prolog; please see
LICENSE for terms of use.

# Release Status

This module is in pre-release and not yet suitable for production use.


# Installation 

To install this module via `pack_install`, run
```prolog
pack_install('https://github.com/mmisamore/clp_term/archive/0.9.zip').
```

# Example Usage

To use this module in your project:
```prolog
:- use_module(library(clp_term)).
```

To post a constraint that `X` is at least `a` in the standard ordering on terms, write:
```prolog
?- term_at_least(X, a).
term_at_least(X, a).
```
Compare to the statement `X @>= a.` which returns `false` even though this is a perfectly good declarative constraint
regarding the possible values of `X`. This module is intended to correct this deficiency. 

There is a corresponding predicate `term_at_most/2`, and one can combine these to produce closed intervals of terms in
the standard ordering:
```prolog
?- term_at_least(X, a), term_at_most(X, c).
term_at_least(X, a),
term_at_most(X, c).
```

These constraints are enforced when the variables are bound, e.g.:
```prolog
?- term_at_least(X, a), term_at_most(X, c), X = b.
X = b.

?- term_at_least(X, a), term_at_most(X, c), X = d.
false.
```
The constraints have been erased due to the unique solutions in these cases.

Upon unification, the constraint intervals are intersected whenever applicable:
```prolog
?- term_at_least(X, a), term_at_least(X, b).
term_at_least(X, b).

?- term_at_least(X, a), term_at_most(X, c), term_at_least(Y, b), term_at_most(Y, d), X = Y.
X = Y,
term_at_least(Y, b),
term_at_most(Y, c)

?- term_at_least(X, a), term_at_most(X, a).
is_singleton_term(X, a).

?- term_at_least(X, b), term_at_most(X, a).
is_empty_term(X).
```

To support comparisons to variables that may *eventually* be bound to terms, one may use `term_at_least/2` and
`term_at_most/2` with variables for constraints:
```prolog
?- term_at_least(X, Y), Y = a.
Y = a,
term_at_least(X, a).

?- term_at_least(X, Y), Y = a, X = b.
X = b,
Y = a.

?- term_at_least(X, Y), X = b.
X = b,
term_at_most(Y, b).

?- term_at_least(X, Y), X = b, Y = a.
X = b,
Y = a.
```
This is a significant departure from the limitations of the predicates `@</2`, etc., which do not provide correct
semantics for these declarative use cases.

A few more predicates are provided to make the underlying domains more transparent and debuggable:
```prolog
?- is_term(X).
is_term(X).
% No constraint on X, but add a domain anyway

?- is_empty_term(X).
is_empty_term(X).
% X unifies with no term whatsoever

?- is_singleton_term(X, Y).
is_singleton_term(X, Y).
% X can only unify with Y, whatever it turns out to be

?- term_at_least(X, a), term_indomain(X, Dom).
Dom = terms_from(const(a)),
term_at_least(X, a).
% Exposes the underlying domain as a term, keeping the constraint 

?- terms_dom_intersection(terms_from(const(a)), terms_to(const(c)), Intersection).
Intersection = [const(a), const(c)].
% Compute the intersection of any two valid domains
```

Due to the presence of variable endpoints, some domain intersections will inevitably yield choicepoints as demanded by
the semantics, e.g.:
```prolog
% Z is forced to be a singleton equal to `a`; or
% Z is in the interval [a, Y]; or
% Z is simply outside the interval, which is possible since Z is still unknown

?- term_at_least(Z, X), term_at_most(Z, Y), X = a.
X = Y, Y = a,
is_singleton_term(Z, a) ;

X = a,
term_at_least(Z, a),
term_at_most(Z, Y) ;

X = a,
is_empty_term(Z).
```


# Technical Details 

This module uses attributed variables to implement an interval theory for the standard ordering on terms.
The underlying theory consists of the following interval types:
* `all_terms` represents the full set of all terms in the standard ordering
* `empty` represents the empty subset of terms in the standard ordering
* `singleton(X)` represents a singleton set of terms in the standard ordering
* `terms_from(X)` represents the half-bounded interval `[X, +oo)`
* `terms_to(Y)` represents the half-bounded interval `(-oo, Y]`
* `[X, Y]` represents a closed interval `[X, Y]` that is not a singleton

The theory implemented here permits known-constant interval endpoints of the form `const(-)` as well as variable
endpoints of the form `variable(-)`. Domain intersections with variable endpoints are non-deterministic.


# Known Limitations and Bugs

* This software has over 400 tests already (see `test/`), but the domain is tricky so some incorrect behaviors are still
likely. If found, please report them to the author so they can be fixed.
* The technical implementation of this module seeks to minimize extraneous choicepoints, but attempts to do this in all
cases have sometimes failed.

