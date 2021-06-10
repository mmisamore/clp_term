# Description
**clp(Term): Constraint Logic Programming for the Standard Ordering of Terms**

This module exposes the standard ordering on Prolog terms as an interval theory, thereby providing fully declarative
replacements for the predicates `@</2`, `@=</2`, `@>/2`, `@>=/2`. It is intended for use with SWI Prolog; please see
LICENSE for terms of use.

# Installation and Usage
To install this module via `pack_install`, run
```
pack_install('https://github.com/mmisamore/clp_term/archive/1.0.0.zip').
```
To use this module in your project:
```
:- use_module(library(clp_term)).
```

# Example Usage




# Theory 
The theory consists of the following interval types:
* `all_terms` represents the full set of all terms in the standard ordering
* `empty` represents the empty subset of terms in the standard ordering
* `singleton(X)` represents a singleton set of terms in the standard ordering
* `terms_from(X)` represents the half-bounded interval `[X, +oo)`
* `terms_to(Y)` represents the half-bounded interval `(-oo, Y]`
* `[X, Y]` represents a closed interval `[X, Y]` that is not a singleton

The domain theory implemented here permits known-constant interval endpoints of the form 
`const(-)` as well as variable endpoints of the form `variable(-)`. Domain intersections with 
variable endpoints are non-deterministic.

