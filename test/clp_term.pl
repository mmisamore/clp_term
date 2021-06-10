:- use_module('../prolog/clp_term').

:- begin_tests(clp_term).

% Tests for term_indomain/2
test('term_indomain_+_+_fails', [ throws(error(uninstantiation_error(1), _)) ]) :-
  clp_term:term_indomain(1, all_terms).

test('term_indomain_+_-_fails', [ throws(error(uninstantiation_error(1), _)) ]) :-
  clp_term:term_indomain(1, _).

test('term_indomain_-_+_succeeds') :-
  clp_term:term_indomain(Term, all_terms),
  get_attr(Term, clp_term, all_terms).

test('term_indomain_-_+_put_twice_unifies', [ fail ]) :-
  clp_term:term_indomain(Term, terms_from(const(1))),
  clp_term:term_indomain(Term, terms_to(const(2))),
  \+ get_attr(Term, clp_term, [const(1), const(2)]).

test('term_indomain_-_-_succeeds') :-
  put_attr(Term, clp_term, all_terms),
  clp_term:term_indomain(Term, Dom),
  Dom == all_terms.

test('term_indomain_-_-_put_get') :-
  clp_term:term_indomain(Term, all_terms),
  clp_term:term_indomain(Term, Dom),
  Dom == all_terms.


% Tests for is_term/1
test('is_term_-_get') :-
  clp_term:is_term(Term),
  get_attr(Term, clp_term, all_terms).

test('is_term_-_already_constrained') :-
  clp_term:term_indomain(Term, terms_from(const(42))),
  clp_term:is_term(Term),
  get_attr(Term, clp_term, terms_from(const(42))).


% Tests for term_at_least/2
test('term_at_least_-_+') :-
  term_at_least(Term, x),
  get_attr(Term, clp_term, terms_from(const(x))).

test('term_at_least_-_-') :-
  term_at_least(Term, X),
  get_attr(Term, clp_term, terms_from(variable(X))).

test('term_at_least_-_+_already_constrained', [ fail ]) :-
  term_at_least(Term, x),
  term_at_least(Term, y),
  \+ get_attr(Term, clp_term, terms_from(const(y))).

% Tests for term_at_most/2
test('term_at_most_-_+') :-
  term_at_most(Term, y),
  get_attr(Term, clp_term, terms_to(const(y))).

test('term_at_most_-_-') :-
  term_at_most(Term, Y),
  get_attr(Term, clp_term, terms_to(variable(Y))).

test('term_at_most_-_+_already_constrained', [ fail ]) :-
  term_at_most(Term, y),
  term_at_most(Term, x),
  \+ get_attr(Term, clp_term, terms_to(const(x))).

% Tests for term_normalized/2
test('term_normalized_c_c') :-
  clp_term:term_normalized(const(a), const(a)).

test('term_normalized_c_-') :-
  clp_term:term_normalized(const(a), Term),
  Term == const(a).

test('term_normalized_v_c') :-
  X = a,
  clp_term:term_normalized(variable(X), const(a)).

test('term_normalized_v_-') :-
  X = a,
  clp_term:term_normalized(variable(X), Term),
  Term == const(a).

test('term_normalized_v_v') :-
  clp_term:term_normalized(variable(X), variable(X)).

test('term_normalized_v_v_-') :-
  clp_term:term_normalized(variable(X), Term),
  Term == variable(X).

test('term_normalized_uninst_const_-_+', [ throws(error(instantiation_error(X), _)) ]) :-
  clp_term:term_normalized(X, const(a)).

test('term_normalized_uninst_var_-_+', [ throws(error(instantiation_error(X), _)) ]) :-
  clp_term:term_normalized(X, variable(_)).

test('term_normalized_uninst_-_-', [ throws(error(instantiation_error(X), _)) ]) :-
  clp_term:term_normalized(X, _).

test('term_normalized_naked_const_+_+', [ fail ]) :-
  clp_term:term_normalized(a, a).

test('term_normalized_unknown_functor_1st_+_+', [ fail ]) :-
  clp_term:term_normalized(foo(_), variable(_)).

test('term_normalized_unknown_functor_2nd_+_+', [ fail ]) :-
  clp_term:term_normalized(variable(_), foo(_)).

test('term_normalized_unknown_functor_1st_+_-', [ fail ]) :-
  clp_term:term_normalized(foo(_), Y),
  Y = variable(_).

test('term_normalized_unknown_functor_2nd_+_-', [ fail ]) :-
  clp_term:term_normalized(variable(_), Y),
  Y = foo(_).

test('term_normalized_naked_const_+_-', [ fail ]) :-
  clp_term:term_normalized(a, _).


% Tests for dom_normalized/2
test('dom_normalized_empty_empty_+_+') :-
  clp_term:dom_normalized(empty, empty).

test('dom_normalized_empty_empty_+_-') :-
  clp_term:dom_normalized(empty, Dom),
  Dom == empty.

test('dom_normalized_all_terms_+_+') :-
  clp_term:dom_normalized(all_terms, all_terms).

test('dom_normalized_all_terms_+_-') :-
  clp_term:dom_normalized(all_terms, Dom),
  Dom == all_terms.

test('dom_normalized_terms_from_+_+_c') :-
  Term0 = const(a),
  clp_term:term_normalized(Term0, Term),
  clp_term:dom_normalized(terms_from(Term0), terms_from(Term)).

test('dom_normalized_terms_from_+_+_v') :-
  Term0 = variable(_),
  clp_term:term_normalized(Term0, Term),
  clp_term:dom_normalized(terms_from(Term0), terms_from(Term)).

test('dom_normalized_terms_from_+_+_v_to_c') :-
  X = a,
  Term0 = variable(X),
  clp_term:term_normalized(Term0, Term),
  clp_term:dom_normalized(terms_from(Term0), terms_from(Term)).

test('dom_normalized_terms_from_+_-_c') :-
  Term0 = const(a),
  clp_term:term_normalized(Term0, Term),
  clp_term:dom_normalized(terms_from(Term0), Dom),
  Dom == terms_from(Term).

test('dom_normalized_terms_from_+_-_v') :-
  Term0 = variable(_),
  clp_term:term_normalized(Term0, Term),
  clp_term:dom_normalized(terms_from(Term0), Dom),
  Dom == terms_from(Term).

test('dom_normalized_terms_from_+_-_v_to_c') :-
  X = a,
  Term0 = variable(X),
  clp_term:term_normalized(Term0, Term),
  clp_term:dom_normalized(terms_from(Term0), Dom),
  Dom == terms_from(Term).

test('dom_normalized_terms_to_+_+_c') :-
  Term0 = const(a),
  clp_term:term_normalized(Term0, Term),
  clp_term:dom_normalized(terms_to(Term0), terms_to(Term)).

test('dom_normalized_terms_to_+_+_v') :-
  Term0 = variable(_),
  clp_term:term_normalized(Term0, Term),
  clp_term:dom_normalized(terms_to(Term0), terms_to(Term)).

test('dom_normalized_terms_to_+_+_v_to_c') :-
  X = a,
  Term0 = variable(X),
  clp_term:term_normalized(Term0, Term),
  clp_term:dom_normalized(terms_to(Term0), terms_to(Term)).

test('dom_normalized_terms_to_+_-_c') :-
  Term0 = const(a),
  clp_term:term_normalized(Term0, Term),
  clp_term:dom_normalized(terms_to(Term0), Dom),
  Dom == terms_to(Term).

test('dom_normalized_terms_to_+_-_v') :-
  Term0 = variable(_),
  clp_term:term_normalized(Term0, Term),
  clp_term:dom_normalized(terms_to(Term0), Dom),
  Dom == terms_to(Term).

test('dom_normalized_terms_to_+_-_v_to_c') :-
  X = a,
  Term0 = variable(X),
  clp_term:term_normalized(Term0, Term),
  clp_term:dom_normalized(terms_to(Term0), Dom),
  Dom == terms_to(Term).

test('dom_normalized_singleton_+_+_c') :-
  Term0 = const(a),
  clp_term:term_normalized(Term0, Term),
  clp_term:dom_normalized(singleton(Term0), singleton(Term)).

test('dom_normalized_singleton_+_+_v') :-
  Term0 = variable(_),
  clp_term:term_normalized(Term0, Term),
  clp_term:dom_normalized(singleton(Term0), singleton(Term)).

test('dom_normalized_singleton_+_+_v_to_c') :-
  X = a,
  Term0 = variable(X),
  clp_term:term_normalized(Term0, Term),
  clp_term:dom_normalized(singleton(Term0), singleton(Term)).

test('dom_normalized_singleton_+_-_c') :-
  Term0 = const(a),
  clp_term:term_normalized(Term0, Term),
  clp_term:dom_normalized(singleton(Term0), Dom),
  Dom == singleton(Term).

test('dom_normalized_singleton_+_-_v') :-
  Term0 = variable(_),
  clp_term:term_normalized(Term0, Term),
  clp_term:dom_normalized(singleton(Term0), Dom),
  Dom == singleton(Term).

test('dom_normalized_singleton_+_-_v_to_c') :-
  X = a,
  Term0 = variable(X),
  clp_term:term_normalized(Term0, Term),
  clp_term:dom_normalized(singleton(Term0), Dom),
  Dom == singleton(Term).

test('dom_normalized_interval_+_+_c_c') :-
  TermX0 = const(a),
  TermY0 = const(b),
  clp_term:term_normalized(TermX0, TermX),
  clp_term:term_normalized(TermY0, TermY),
  clp_term:dom_normalized([TermX0, TermY0], [TermX, TermY]).

test('dom_normalized_interval_+_+_c_v') :-
  TermX0 = const(a),
  TermY0 = variable(_),
  clp_term:term_normalized(TermX0, TermX),
  clp_term:term_normalized(TermY0, TermY),
  clp_term:dom_normalized([TermX0, TermY0], [TermX, TermY]).

test('dom_normalized_interval_+_+_v_c') :-
  TermX0 = variable(_),
  TermY0 = const(b),
  clp_term:term_normalized(TermX0, TermX),
  clp_term:term_normalized(TermY0, TermY),
  clp_term:dom_normalized([TermX0, TermY0], [TermX, TermY]).

test('dom_normalized_interval_+_+_v_v') :-
  TermX0 = variable(_),
  TermY0 = variable(_),
  clp_term:term_normalized(TermX0, TermX),
  clp_term:term_normalized(TermY0, TermY),
  clp_term:dom_normalized([TermX0, TermY0], [TermX, TermY]).

test('dom_normalized_interval_+_+_v_v2c') :-
  TermX0 = variable(_),
  TermY0 = variable(Y),
  Y = b,
  clp_term:term_normalized(TermX0, TermX),
  clp_term:term_normalized(TermY0, TermY),
  clp_term:dom_normalized([TermX0, TermY0], [TermX, TermY]).

test('dom_normalized_interval_+_+_v2c_v') :-
  TermX0 = variable(X),
  TermY0 = variable(_),
  X = a,
  clp_term:term_normalized(TermX0, TermX),
  clp_term:term_normalized(TermY0, TermY),
  clp_term:dom_normalized([TermX0, TermY0], [TermX, TermY]).

test('dom_normalized_interval_+_+_v2c_v2c') :-
  TermX0 = variable(X),
  TermY0 = variable(Y),
  X = a,
  Y = b,
  clp_term:term_normalized(TermX0, TermX),
  clp_term:term_normalized(TermY0, TermY),
  clp_term:dom_normalized([TermX0, TermY0], [TermX, TermY]).

test('dom_normalized_interval_+_-_c_c') :-
  TermX0 = const(a),
  TermY0 = const(b),
  clp_term:term_normalized(TermX0, TermX),
  clp_term:term_normalized(TermY0, TermY),
  clp_term:dom_normalized([TermX0, TermY0], Dom),
  Dom == [TermX, TermY].

test('dom_normalized_interval_+_-_c_v') :-
  TermX0 = const(a),
  TermY0 = variable(_),
  clp_term:term_normalized(TermX0, TermX),
  clp_term:term_normalized(TermY0, TermY),
  clp_term:dom_normalized([TermX0, TermY0], Dom),
  Dom == [TermX, TermY].

test('dom_normalized_interval_+_-_v_c') :-
  TermX0 = variable(_),
  TermY0 = const(b),
  clp_term:term_normalized(TermX0, TermX),
  clp_term:term_normalized(TermY0, TermY),
  clp_term:dom_normalized([TermX0, TermY0], Dom),
  Dom == [TermX, TermY].

test('dom_normalized_interval_+_-_v_v') :-
  TermX0 = variable(_),
  TermY0 = variable(_),
  clp_term:term_normalized(TermX0, TermX),
  clp_term:term_normalized(TermY0, TermY),
  clp_term:dom_normalized([TermX0, TermY0], Dom),
  Dom == [TermX, TermY].

test('dom_normalized_interval_+_-_v_v2c') :-
  TermX0 = variable(_),
  TermY0 = variable(Y),
  Y = b,
  clp_term:term_normalized(TermX0, TermX),
  clp_term:term_normalized(TermY0, TermY),
  clp_term:dom_normalized([TermX0, TermY0], Dom),
  Dom == [TermX, TermY].

test('dom_normalized_interval_+_-_v2c_v') :-
  TermX0 = variable(X),
  TermY0 = variable(_),
  X = a,
  clp_term:term_normalized(TermX0, TermX),
  clp_term:term_normalized(TermY0, TermY),
  clp_term:dom_normalized([TermX0, TermY0], Dom),
  Dom == [TermX, TermY].

test('dom_normalized_interval_+_-_v2c_v2c') :-
  TermX0 = variable(X),
  TermY0 = variable(Y),
  X = a,
  Y = b,
  clp_term:term_normalized(TermX0, TermX),
  clp_term:term_normalized(TermY0, TermY),
  clp_term:dom_normalized([TermX0, TermY0], Dom),
  Dom == [TermX, TermY].

test('dom_normalized_interval_+_+_c_c_sing') :-
  clp_term:dom_normalized([const(a), const(a)], singleton(const(a))).

test('dom_normalized_interval_+_+_c_v2c_sing') :-
  Y = a,
  clp_term:dom_normalized([const(a), variable(Y)], singleton(const(a))).

test('dom_normalized_interval_+_+_v2c_c_sing') :-
  X = a,
  clp_term:dom_normalized([variable(X), const(a)], singleton(const(a))).

test('dom_normalized_interval_+_+_v2c_v2c_sing') :-
  X = a, Y = a,
  clp_term:dom_normalized([variable(X), variable(Y)], singleton(const(a))).

test('dom_normalized_interval_+_+_v_v_eq_sing') :-
  X = Y,
  clp_term:dom_normalized([variable(X), variable(Y)], singleton(variable(X))).

test('dom_normalized_interval_+_-_c_c_sing') :-
  clp_term:dom_normalized([const(a), const(a)], Dom),
  Dom = singleton(const(a)).

test('dom_normalized_interval_+_-_c_v2c_sing') :-
  Y = a,
  clp_term:dom_normalized([const(a), variable(Y)], Dom),
  Dom = singleton(const(a)).

test('dom_normalized_interval_+_-_v2c_c_sing') :-
  X = a,
  clp_term:dom_normalized([variable(X), const(a)], Dom),
  Dom = singleton(const(a)).

test('dom_normalized_interval_+_-_v2c_v2c_sing') :-
  X = a, Y = a,
  clp_term:dom_normalized([variable(X), variable(Y)], Dom),
  Dom = singleton(const(a)).

test('dom_normalized_interval_+_-_v_v_eq_sing') :-
  X = Y,
  clp_term:dom_normalized([variable(X), variable(Y)], Dom),
  Dom = singleton(variable(X)).

test('dom_normalized_+_+_unknown_functor_1st', [ fail ]) :-
  X = a,
  clp_term:dom_normalized(foo(variable(X)), terms_from(const(a))).

test('dom_normalized_+_+_unknown_functor_2nd', [ fail ]) :-
  X = a,
  clp_term:dom_normalized(terms_from(variable(X)), foo(const(a))).

test('dom_normalized_+_+_functors_dont_match', [ fail ]) :-
  X = a,
  clp_term:dom_normalized(terms_from(variable(X)), terms_to(const(a))).

test('dom_normalized_+_+_uninstantiated_endpoint', [ throws(error(instantiation_error(X), _)) ]) :-
  clp_term:dom_normalized(terms_from(X), terms_from(const(a))).

test('dom_normalized_-_+_uninstantiated_1st', [ fail ]) :-
  clp_term:dom_normalized(_, all_terms).

test('dom_normalized_+_-_unknown_functor_1st', [ fail ]) :-
  X = a,
  clp_term:dom_normalized(foo(variable(X)), _).

test('dom_normalized_+_-_unknown_functor_2nd', [ fail ]) :-
  X = a,
  clp_term:dom_normalized(terms_from(variable(X)), Y),
  Y = foo(const(a)).

test('dom_normalized_+_-_functors_dont_match', [ fail ]) :-
  X = a,
  clp_term:dom_normalized(terms_from(variable(X)), Y),
  Y = terms_to(const(a)).

test('dom_normalized_+_-_uninstantiated_endpoint', [ throws(error(instantiation_error(X), _)) ]) :-
  clp_term:dom_normalized(terms_from(X), Y),
  Y = terms_from(const(a)).


% Tests for terms_intersection_from_from/3
test('terms_from_from_intersection_c_c_>=') :-
  setof(I, clp_term:terms_intersection_from_from(terms_from(const(y)), terms_from(const(x)), I), [terms_from(const(y))]).

test('terms_from_from_intersection_c_c_<') :-
  setof(I, clp_term:terms_intersection_from_from(terms_from(const(x)), terms_from(const(y)), I), [terms_from(const(y))]).

test('terms_from_from_intersection_c_v') :-
  setof(Y-I, clp_term:terms_intersection_from_from(terms_from(const(x)), terms_from(variable(Y)), I), Ans),
  Ans = [Y-terms_from(variable(Y)), Y-terms_from(const(x))].

test('terms_from_from_intersection_v_c') :-
  setof(X-I, clp_term:terms_intersection_from_from(terms_from(variable(X)), terms_from(const(y)), I), Ans),
  Ans = [X-terms_from(const(y)), X-terms_from(variable(X))].

test('terms_from_from_intersection_v_v') :-
  setof(X-Y-I, clp_term:terms_intersection_from_from(terms_from(variable(X)), terms_from(variable(Y)), I), Ans),
  Ans = [X-Y-terms_from(variable(X)), X-Y-terms_from(variable(Y))].


% Tests for terms_intersection_to_to/3
test('terms_to_to_intersection_c_c_>=') :-
  setof(I, clp_term:terms_intersection_to_to(terms_to(const(y)), terms_to(const(x)), I), [terms_to(const(x))]).

test('terms_to_to_intersection_c_c_<') :-
  setof(I, clp_term:terms_intersection_to_to(terms_to(const(x)), terms_to(const(y)), I), [terms_to(const(x))]).

test('terms_to_to_intersection_c_v') :-
  setof(Y-I, clp_term:terms_intersection_to_to(terms_to(const(x)), terms_to(variable(Y)), I), Ans),
  Ans = [Y-terms_to(variable(Y)), Y-terms_to(const(x))].

test('terms_to_to_intersection_v_c') :-
  setof(X-I, clp_term:terms_intersection_to_to(terms_to(variable(X)), terms_to(const(y)), I), Ans),
  Ans = [X-terms_to(const(y)), X-terms_to(variable(X))].

test('terms_to_to_intersection_v_v') :-
  setof(X-Y-I, clp_term:terms_intersection_to_to(terms_to(variable(X)), terms_to(variable(Y)), I), Ans),
  Ans = [X-Y-terms_to(variable(X)), X-Y-terms_to(variable(Y))].


% Tests for terms_intersection_from_to/3
test('terms_from_to_intersection_c_c_=') :-
  setof(I, clp_term:terms_intersection_from_to(terms_from(const(x)), terms_to(const(x)), I), [singleton(const(x))]).

test('terms_from_to_intersection_c_c_<') :-
  setof(I, clp_term:terms_intersection_from_to(terms_from(const(x)), terms_to(const(y)), I), [[const(x), const(y)]]).

test('terms_from_to_intersection_c_c_>') :-
  setof(I, clp_term:terms_intersection_from_to(terms_from(const(y)), terms_to(const(x)), I), [empty]).

test('terms_from_to_intersection_c_v') :-
  setof(Y-I, clp_term:terms_intersection_from_to(terms_from(const(x)), terms_to(variable(Y)), I), Ans),
  Ans = [Y-empty, Y-[const(x), variable(Y)], Y-singleton(const(x))].

test('terms_from_to_intersection_c_v_unified') :-
  setof(Y, clp_term:terms_intersection_from_to(terms_from(const(x)), terms_to(variable(Y)), singleton(const(x))), [Y1]),
  Y1 == x.

test('terms_from_to_intersection_v_c') :-
  setof(X-I, clp_term:terms_intersection_from_to(terms_from(variable(X)), terms_to(const(y)), I), Ans),
  Ans = [X-empty, X-[variable(X), const(y)], X-singleton(const(y))].

test('terms_from_to_intersection_v_c_unified') :-
  setof(X, clp_term:terms_intersection_from_to(terms_from(variable(X)), terms_to(const(y)), singleton(const(y))), [X1]),
  X1 == y.

test('terms_from_to_intersection_v_v') :-
  setof(X-Y-I, clp_term:terms_intersection_from_to(terms_from(variable(X)), terms_to(variable(Y)), I), Ans),
  Ans = [X-Y-empty, X-Y-[variable(X), variable(Y)], X-Y-singleton(variable(X))].

test('terms_from_to_intersection_v_v_unified') :-
  setof(X-Y, clp_term:terms_intersection_from_to(terms_from(variable(X)), terms_to(variable(Y)), singleton(variable(X))), [X1-Y1]),
  X1 == Y1.

test('terms_from_to_intersection_v_v_not_interval_if_identical', [ fail ]) :-
  X = Y,
  clp_term:terms_intersection_from_to(terms_from(variable(X)), terms_to(variable(Y)), [variable(X), variable(Y)]).


% Tests for terms_intersection_to_from/3
test('terms_to_from_intersection_agrees_with_from_to') :-
  setof(X-Y-ToFrom, clp_term:terms_intersection_to_from(terms_to(variable(X)), terms_from(variable(Y)), ToFrom), ToFroms),
  setof(X-Y-FromTo, clp_term:terms_intersection_from_to(terms_from(variable(Y)), terms_to(variable(X)), FromTo), ToFroms).


% Tests for terms_intersection_from_int/3
% | x R y | x R z | Out                      |
% |   ?   |   ?   |  [y, z]; [x, z]; [z]; [] |
% |   ?   |   <   |  [y, z]; [x, z]          |
% |   ?   |   =   |  [z]                     |
% |   ?   |   >   |  []                      |
% |   <   |   ?   |  [y,z]                   |
% |   <   |   <   |  [y,z]                   |
% |   =   |   <   |  [y,z]                   |
% |   >   |   ?   |  [x,z]; [z]; []          |
% |   >   |   <   |  [x,z]                   |
% |   >   |   =   |  [z]                     |
% |   >   |   >   |  []                      |
test('terms_from_int_intersection_?_?') :-
  setof(Y-Z-I, clp_term:terms_intersection_from_int(terms_from(const(a)), [variable(Y), variable(Z)], I), Ans),
  Ans = [Y-Z-empty, Y-Z-singleton(const(a)), Y-Z-[const(a), variable(Z)], Y-Z-[variable(Y), variable(Z)]].

test('terms_from_int_intersection_?_?_unified') :-
  setof(Z, clp_term:terms_intersection_from_int(terms_from(const(a)), [variable(_), variable(Z)], singleton(const(a))), [Z1]),
  Z1 == a.

test('terms_from_int_intersection_?_<') :-
  setof(Y-I, clp_term:terms_intersection_from_int(terms_from(const(a)), [variable(Y), const(c)], I), Ans),
  Ans = [Y-[const(a), const(c)], Y-[variable(Y), const(c)]].

test('terms_from_int_intersection_?_=') :-
  clp_term:terms_intersection_from_int(terms_from(const(a)), [variable(_), const(a)], singleton(const(a))).

test('terms_from_int_intersection_?_>') :-
  clp_term:terms_intersection_from_int(terms_from(const(b)), [variable(_), const(a)], empty).

test('terms_from_int_intersection_<_?') :-
  clp_term:terms_intersection_from_int(terms_from(const(a)), [const(b), variable(Z)], [const(b), variable(Z)]).

test('terms_from_int_intersection_<_<') :-
  clp_term:terms_intersection_from_int(terms_from(const(a)), [const(b), const(c)], [const(b), const(c)]).

test('terms_from_int_intersection_=_<') :-
  clp_term:terms_intersection_from_int(terms_from(const(a)), [const(a), const(b)], [const(a), const(b)]).

test('terms_from_int_intersection_>_?') :-
  setof(Z-I, clp_term:terms_intersection_from_int(terms_from(const(b)), [const(a), variable(Z)], I), Ans),
  Ans = [Z-empty, Z-[const(b), variable(Z)], Z-singleton(const(b))].

test('terms_from_int_intersection_>_?_unified') :-
  setof(Z, clp_term:terms_intersection_from_int(terms_from(const(b)), [const(a), variable(Z)], singleton(const(b))), [Z1]),
  Z1 == b.

test('terms_from_int_intersection_>_<') :-
  clp_term:terms_intersection_from_int(terms_from(const(b)), [const(a), const(c)], [const(b), const(c)]).

test('terms_from_int_intersection_>_=') :-
  clp_term:terms_intersection_from_int(terms_from(const(b)), [const(a), const(b)], singleton(const(b))).

test('terms_from_int_intersection_>_>') :-
  clp_term:terms_intersection_from_int(terms_from(const(c)), [const(a), const(b)], empty).


% Tests for terms_intersection_int_from/3
test('terms_int_from_intersection_agrees_with_from_int', [ fail ]) :-
  member(X, [const(1), variable(_)]),
  member(Y, [const(3), variable(_)]),
  member(Z, [const(2), variable(_)]),
  setof(X-Y-Z-IntFrom, clp_term:terms_intersection_int_from([X, Y], terms_from(Z), IntFrom), IntFroms),
  \+ setof(X-Y-Z-FromInt, clp_term:terms_intersection_from_int(terms_from(Z), [X, Y], FromInt), IntFroms).


% Tests for terms_intersection_to_int/3
% | x R y | x R z | Out                   |
% |   ?   |   ?   | [y,z]; [y,x]; [y]; [] |
% |   ?   |   <   | [y,x]; [y]; []        |
% |   ?   |   =   | [y,z]                 |
% |   ?   |   >   | [y,z]                 |
% |   <   |   ?   | []                    |
% |   <   |   <   | []                    |
% |   =   |   <   | [y]                   |
% |   =   |   ?   | [y]                   |
% |   >   |   ?   | [y,x]; [y,z]          |
% |   >   |   <   | [y,x]                 |
% |   >   |   =   | [y,z]                 |
% |   >   |   >   | [y,z]                 |
test('terms_to_int_intersection_?_?') :-
  setof(Y-Z-I, clp_term:terms_intersection_to_int(terms_to(const(a)), [variable(Y), variable(Z)], I), Ans),
  Ans = [Y-Z-empty, Y-Z-[variable(Y), const(a)], Y-Z-[variable(Y), variable(Z)], Y-Z-singleton(const(a))].

test('terms_to_int_intersection_?_?_unified') :-
  setof(Y, clp_term:terms_intersection_to_int(terms_to(const(a)), [variable(Y), variable(_)], singleton(const(a))), [Y1]),
  Y1 == a.

test('terms_to_int_intersection_?_<') :-
  setof(Y-I, clp_term:terms_intersection_to_int(terms_to(const(a)), [variable(Y), const(c)], I), Ans),
  Ans = [Y-empty, Y-[variable(Y), const(a)], Y-singleton(const(a))].

test('terms_to_int_intersection_?_<_unified') :-
  setof(Y, clp_term:terms_intersection_to_int(terms_to(const(a)), [variable(Y), const(c)], singleton(const(a))), [Y1]),
  Y1 == a.

test('terms_to_int_intersection_?_=') :-
  clp_term:terms_intersection_to_int(terms_to(const(a)), [variable(Y), const(a)], [variable(Y), const(a)]).

test('terms_to_int_intersection_?_>') :-
  clp_term:terms_intersection_to_int(terms_to(const(b)), [variable(Y), const(a)], [variable(Y), const(a)]).

test('terms_to_int_intersection_<_?') :-
  clp_term:terms_intersection_to_int(terms_to(const(a)), [const(b), variable(_)], empty).

test('terms_to_int_intersection_<_<') :-
  clp_term:terms_intersection_to_int(terms_to(const(a)), [const(b), const(c)], empty).

test('terms_to_int_intersection_=_<') :-
  clp_term:terms_intersection_to_int(terms_to(const(a)), [const(a), const(b)], singleton(const(a))).

test('terms_to_int_intersection_=_?') :-
  clp_term:terms_intersection_to_int(terms_to(const(a)), [const(a), variable(_)], singleton(const(a))).

test('terms_to_int_intersection_>_?') :-
  setof(Z-I, clp_term:terms_intersection_to_int(terms_to(const(b)), [const(a), variable(Z)], I), Ans),
  Ans = [Z-[const(a), variable(Z)], Z-[const(a), const(b)]].

test('terms_to_int_intersection_>_<') :-
  clp_term:terms_intersection_to_int(terms_to(const(b)), [const(a), const(c)], [const(a), const(b)]).

test('terms_to_int_intersection_>_=') :-
  clp_term:terms_intersection_to_int(terms_to(const(b)), [const(a), const(b)], [const(a), const(b)]).

test('terms_to_int_intersection_>_>') :-
  clp_term:terms_intersection_to_int(terms_to(const(c)), [const(a), const(b)], [const(a), const(b)]).


% Tests for terms_intersection_int_to/3
test('terms_int_to_intersection_agrees_with_to_int', [ fail ]) :-
  member(X, [const(1), variable(_)]),
  member(Y, [const(3), variable(_)]),
  member(Z, [const(2), variable(_)]),
  setof(X-Y-Z-IntTo, clp_term:terms_intersection_int_to([X, Y], terms_to(Z), IntTo), IntTos),
  \+ setof(X-Y-Z-ToInt, clp_term:terms_intersection_to_int(terms_to(Z), [X, Y], ToInt), IntTos).


% Tests for terms_intersection_int_int/3
% | xRz | xRw | yRz | yRw | Out                        | Analysis
% |     |     |  <  |     | empty                      | [xy][zw]
% |     |  >  |     |     | empty                      | [zw][xy]
% |     |     |  =  |     | [y]                        | [x[y]w]
% |     |  =  |     |     | [x]                        | [z[x]y]
test('terms_int_int_intersection_y<z') :-
  clp_term:terms_intersection_int_int([variable(_), const(b)], [const(c), variable(_)], empty).

test('terms_int_int_intersection_x>w') :-
  clp_term:terms_intersection_int_int([const(b), variable(_)], [variable(_), const(a)], empty).

test('terms_int_int_intersection_y=z') :-
  clp_term:terms_intersection_int_int([variable(_), const(b)], [const(b), variable(_)], singleton(const(b))).

test('terms_int_int_intersection_x=w') :-
  clp_term:terms_intersection_int_int([const(a), variable(_)], [variable(_), const(a)], singleton(const(a))).

% | xRz | xRw | yRz | yRw | Out                        | Analysis
% |  <  |  <  |  >  |  <  | [z,y]                      | [x[zy]w]
% |  <  |  <  |  >  |  =  | [z,y]                      | [x[zy]y]
% |  <  |  <  |  >  |  >  | [z,w]                      | [x[zw]y]
test('terms_int_int_intersection_<_<_>_<') :-
  clp_term:terms_intersection_int_int([const(a), const(c)], [const(b), const(d)], [const(b), const(c)]).

test('terms_int_int_intersection_<_<_>_=') :-
  clp_term:terms_intersection_int_int([const(a), const(c)], [const(b), const(c)], [const(b), const(c)]).

test('terms_int_int_intersection_<_<_>_>') :-
  clp_term:terms_intersection_int_int([const(a), const(d)], [const(b), const(c)], [const(b), const(c)]).

% | xRz | xRw | yRz | yRw | Out                        | Analysis
% |  <  |  <  |  ?  |  ?  | [z,w]; [z,y]; [z]; empty   | [x[zw]y] or [x[zy]w] or [xy][zw]
test('terms_int_int_intersection_<_<_?_?') :-
  setof(Y-I, clp_term:terms_intersection_int_int([const(a), variable(Y)], [const(b), const(c)], I), Ans),
  Ans = [Y-empty, Y-[const(b), variable(Y)], Y-[const(b), const(c)], Y-singleton(const(b))].

test('terms_int_int_intersection_<_<_?_?_unified') :-
  setof(Y, clp_term:terms_intersection_int_int([const(a), variable(Y)], [const(b), const(c)], singleton(const(b))), [Y1]),
  Y1 == b.

% | xRz | xRw | yRz | yRw | Out                        | Analysis
% |  <  |  ?  |  >  |  ?  | [z,w]; [z,y]               | [x[zw]y] or [x[zy]w]
test('terms_int_int_intersection_<_?_>_?') :-
  setof(W-I, clp_term:terms_intersection_int_int([const(a), const(c)], [const(b), variable(W)], I), Ans),
  Ans = [W-[const(b), const(c)], W-[const(b), variable(W)]].

% | xRz | xRw | yRz | yRw | Out                        | Analysis
% |  <  |  ?  |  ?  |  ?  | [z,w]; [z,y]; [y]; empty   | [x[zw]y] or [x[zy]w] or [xy][zw]
test('terms_int_int_intersection_<_?_?_?') :-
  setof(Y-W-I, clp_term:terms_intersection_int_int([const(a), variable(Y)], [const(c), variable(W)], I), Ans),
  Ans = [Y-W-empty, Y-W-[const(c), variable(Y)], Y-W-[const(c), variable(W)], Y-W-singleton(const(c))].

test('terms_int_int_intersection_<_?_?_?_unified') :-
  setof(Y, clp_term:terms_intersection_int_int([const(a), variable(Y)], [const(c), variable(_)], singleton(const(c))), [Y1]),
  Y1 == c.

% | xRz | xRw | yRz | yRw | Out                        | Analysis
% |  =  |  <  |  >  |  <  | [z,y]                      | [[zy]w]
% |  =  |  <  |  >  |  =  | [z,y]                      | [[zy]y]
% |  =  |  <  |  >  |  >  | [z,w]                      | [[zw]y]
test('terms_int_int_intersection_=_<_>_<') :-
  clp_term:terms_intersection_int_int([const(a), const(b)], [const(a), const(d)], [const(a), const(b)]).

test('terms_int_int_intersection_=_<_>_=') :-
  clp_term:terms_intersection_int_int([const(a), const(d)], [const(a), const(d)], [const(a), const(d)]).

test('terms_int_int_intersection_=_<_>_>') :-
  clp_term:terms_intersection_int_int([const(a), const(d)], [const(a), const(c)], [const(a), const(c)]).

% | xRz | xRw | yRz | yRw | Out                        | Analysis
% |  =  |  <  |  ?  |  ?  | [z,w]; [z,y]               | [[zw]y] or [[zy]w]
test('terms_int_int_intersection_=_<_?_?') :-
  setof(Y-I, clp_term:terms_intersection_int_int([const(a), variable(Y)], [const(a), const(d)], I), Ans),
  Ans = [Y-[const(a), variable(Y)], Y-[const(a), const(d)]].

% | xRz | xRw | yRz | yRw | Out                        | Analysis
% |  =  |  ?  |  >  |  ?  | [z,w]; [z,y]               | [[zw]y] or [[zy]w]
test('terms_int_int_intersection_=_?_>_?') :-
  setof(W-I, clp_term:terms_intersection_int_int([const(a), const(b)], [const(a), variable(W)], I), Ans),
  Ans = [W-[const(a), const(b)], W-[const(a), variable(W)]].

% | xRz | xRw | yRz | yRw | Out                        | Analysis
% |  =  |  ?  |  ?  |  ?  | [z,w]; [z,y]               | [[zw]y] or [[zy]w]
test('terms_int_int_intersection_=_?_?_?') :-
  setof(Y-W-I, clp_term:terms_intersection_int_int([const(a), variable(Y)], [const(a), variable(W)], I), Ans),
  Ans = [Y-W-[const(a), variable(Y)], Y-W-[const(a), variable(W)]].

% | xRz | xRw | yRz | yRw | Out                        | Analysis
% |  >  |  <  |  >  |  <  | [x,y]                      | [z[xy]w]
% |  >  |  <  |  >  |  =  | [x,y]                      | [z[xy]y]
% |  >  |  <  |  >  |  >  | [x,w]                      | [z[xw]y]
test('terms_int_int_intersection_>_<_>_<') :-
  clp_term:terms_intersection_int_int([const(b), const(c)], [const(a), const(d)], [const(b), const(c)]).

test('terms_int_int_intersection_>_<_>_=') :-
  clp_term:terms_intersection_int_int([const(b), const(c)], [const(a), const(c)], [const(b), const(c)]).

test('terms_int_int_intersection_>_<_>_>') :-
  clp_term:terms_intersection_int_int([const(b), const(d)], [const(a), const(c)], [const(b), const(c)]).

% | xRz | xRw | yRz | yRw | Out                        | Analysis
% |  >  |  <  |  ?  |  ?  | [x,w]; [x,y]               | [z[xw]y] or [z[xy]w]
test('terms_int_int_intersection_>_<_?_?') :-
  setof(Y-I, clp_term:terms_intersection_int_int([const(c), variable(Y)], [const(a), const(d)], I), Ans),
  Ans = [Y-[const(c), variable(Y)], Y-[const(c), const(d)]].

% | xRz | xRw | yRz | yRw | Out                        | Analysis
% |  >  |  ?  |  >  |  ?  | [x,w]; [x,y]; [x]; empty   | [z[xw]y] or [z[xy]w] or [zw][xy]
test('terms_int_int_intersection_>_?_>_?') :-
  setof(W-I, clp_term:terms_intersection_int_int([const(b), const(c)], [const(a), variable(W)], I), Ans),
  Ans = [W-empty, W-[const(b), const(c)], W-[const(b), variable(W)], W-singleton(const(b))].

test('terms_int_int_intersection_>_?_>_?_unified') :-
  setof(W, clp_term:terms_intersection_int_int([const(b), const(c)], [const(a), variable(W)], singleton(const(b))), [W1]),
  W1 == b.

% | xRz | xRw | yRz | yRw | Out                        | Analysis
% |  >  |  ?  |  ?  |  ?  | [x,w]; [x,y]; [x]; empty   | [z[xw]y] or [z[xy]w] or [zw][xy]
test('terms_int_int_intersection_>_?_?_?') :-
  setof(Y-W-I, clp_term:terms_intersection_int_int([const(c), variable(Y)], [const(a), variable(W)], I), Ans),
  Ans = [Y-W-empty, Y-W-singleton(const(c)), Y-W-[const(c), variable(Y)], Y-W-[const(c), variable(W)]].

test('terms_int_int_intersection_>_?_?_?_unified') :-
  setof(W, clp_term:terms_intersection_int_int([const(c), variable(_)], [const(a), variable(W)], singleton(const(c))), [W1]),
  W1 == c.

% | xRz | xRw | yRz | yRw | Out                        | Analysis
% |  ?  |  <  |  ?  |  <  | [z,y]; [x,y]; [y]; empty   | [z[xy]w] or [x[zy]w] or [xy][zw]
% |  ?  |  <  |  ?  |  =  | [z,y]; [x,y]               | [z[xy]] or [x[zy]]
% |  ?  |  <  |  ?  |  >  | [z,w]; [x,w]               | [z[xw]y] or [x[zw]y]
% |  ?  |  <  |  ?  |  ?  | [z,w]; [x,w]; [z,y];       |
%                         | [x,y]; [y]; empty          |
test('terms_int_int_intersection_?_<_?_<') :-
  setof(Z-I, clp_term:terms_intersection_int_int([const(a), const(b)], [variable(Z), const(d)], I), Ans),
  Ans = [Z-empty, Z-[const(a), const(b)], Z-[variable(Z), const(b)], Z-singleton(const(b))].

test('terms_int_int_intersection_?_<_?_<_unified') :-
  setof(Z, clp_term:terms_intersection_int_int([const(a), const(b)], [variable(Z), const(d)], singleton(const(b))), [Z1]),
  Z1 == b.

test('terms_int_int_intersection_?_<_?_=') :-
  setof(Z-I, clp_term:terms_intersection_int_int([const(a), const(b)], [variable(Z), const(b)], I), Ans),
  Ans = [Z-[const(a), const(b)], Z-[variable(Z), const(b)]].

test('terms_int_int_intersection_?_<_?_>') :-
  setof(Z-I, clp_term:terms_intersection_int_int([const(a), const(c)], [variable(Z), const(b)], I), Ans),
  Ans = [Z-[const(a), const(b)], Z-[variable(Z), const(b)]].

test('terms_int_int_intersection_?_<_?_?') :-
  setof(Y-Z-I, clp_term:terms_intersection_int_int([const(a), variable(Y)], [variable(Z), const(b)], I), Ans),
  Ans = [Y-Z-empty, Y-Z-singleton(variable(Y)), Y-Z-[const(a), variable(Y)], Y-Z-[variable(Z), variable(Y)],
         Y-Z-[const(a), const(b)], Y-Z-[variable(Z), const(b)]].

test('terms_int_int_intersection_?_<_?_?_v') :-
  setof(Y-Z, clp_term:terms_intersection_int_int([const(a), variable(Y)], [variable(Z), const(b)], singleton(variable(Y))), [Y1-Z1]),
  Y1 == Z1.

% | xRz | xRw | yRz | yRw | Out                        | Analysis
% |  ?  |  ?  |  >  |  <  | [z,y]; [x,y]               | [x[zy]w] or [z[xy]w]
% |  ?  |  ?  |  >  |  =  | [z,y]; [x,y]               | [x[zy]] or [z[xy]]
% |  ?  |  ?  |  >  |  >  | [z,w]; [x,w]; [x]; empty   | [x[zw]y] or [z[xw]y] or [zw][xy]
% |  ?  |  ?  |  >  |  ?  | [z,w]; [x,w]; [z,y];       |
%                         | [x,y]; [x]; empty          |
test('terms_int_int_intersection_?_?_>_<') :-
  setof(X-I, clp_term:terms_intersection_int_int([variable(X), const(c)], [const(b), const(d)], I), Ans),
  Ans = [X-[variable(X), const(c)], X-[const(b), const(c)]].

test('terms_int_int_intersection_?_?_>_=') :-
  setof(X-I, clp_term:terms_intersection_int_int([variable(X), const(c)], [const(b), const(c)], I), Ans),
  Ans = [X-[variable(X), const(c)], X-[const(b), const(c)]].

test('terms_int_int_intersection_?_?_>_>') :-
  setof(X-I, clp_term:terms_intersection_int_int([variable(X), const(d)], [const(b), const(c)], I), Ans),
  Ans = [X-empty, X-[variable(X), const(c)], X-[const(b), const(c)], X-singleton(const(c))].

test('terms_int_int_intersection_?_?_>_>_X==c') :-
  setof(X, clp_term:terms_intersection_int_int([variable(X), const(d)], [const(b), const(c)], singleton(const(c))), [X1]),
  X1 == c.

test('terms_int_int_intersection_?_?_>_?') :-
  setof(X-W-I, clp_term:terms_intersection_int_int([variable(X), const(c)], [const(b), variable(W)], I), Ans),
  Ans = [X-W-empty, X-W-singleton(variable(X)), X-W-[variable(X), const(c)], X-W-[const(b), const(c)],
         X-W-[variable(X), variable(W)], X-W-[const(b), variable(W)]].

test('terms_int_int_intersection_?_?_>_?_v') :-
  setof(X-W, clp_term:terms_intersection_int_int([variable(X), const(c)], [const(b), variable(W)], singleton(variable(X))), [X1-W1]),
  X1 == W1.

% | xRz | xRw | yRz | yRw | Out                        | Analysis
% |  ?  |  ?  |  ?  |  <  | [x,y]; [z,y]; [y]; empty   | [z[xy]w] or [x[zy]w] or [xy][zw]
% |  ?  |  ?  |  ?  |  =  | [x,y]; [z,y]               | [x[zy]] or [z[xy]]
% |  ?  |  ?  |  ?  |  >  | [z,w]; [x,w]; [x]; empty   | [x[zw]y] or [z[xw]y] or [zw][xy]
% |  ?  |  ?  |  ?  |  ?  | [z,w]; [x,w]; [z,y];       |
%                         | [x,y]; [x]; [y]; empty     |
test('terms_int_int_intersection_?_?_?_<') :-
  setof(X-Z-I, clp_term:terms_intersection_int_int([variable(X), const(b)], [variable(Z), const(d)], I), Ans),
  Ans = [X-Z-empty, X-Z-singleton(const(b)), X-Z-[variable(X), const(b)], X-Z-[variable(Z), const(b)]].

test('terms_int_int_intersection_?_?_?_<_Z==b') :-
  setof(Z, clp_term:terms_intersection_int_int([variable(_), const(b)], [variable(Z), const(d)], singleton(const(b))), [Z1]),
  Z1 == b.

test('terms_int_int_intersection_?_?_?_=') :-
  setof(X-Z-I, clp_term:terms_intersection_int_int([variable(X), const(b)], [variable(Z), const(b)], I), Ans),
  Ans = [X-Z-[variable(X), const(b)], X-Z-[variable(Z), const(b)]].

test('terms_int_int_intersection_?_?_?_>') :-
  setof(X-Z-I, clp_term:terms_intersection_int_int([variable(X), const(d)], [variable(Z), const(b)], I), Ans),
  Ans = [X-Z-empty, X-Z-[variable(Z), const(b)], X-Z-[variable(X), const(b)], X-Z-singleton(const(b))].

test('terms_int_int_intersection_?_?_?_>_X==b') :-
  setof(X, clp_term:terms_intersection_int_int([variable(X), const(d)], [variable(_), const(b)], singleton(const(b))), [X1]),
  X1 == b.

test('terms_int_int_intersection_?_?_?_?') :-
  setof(X-Y-Z-W-I, clp_term:terms_intersection_int_int([variable(X), variable(Y)], [variable(Z), variable(W)], I), Ans),
  Ans = [X-Y-Z-W-empty, X-Y-Z-W-singleton(variable(Y)), X-Y-Z-W-singleton(variable(X)),
         X-Y-Z-W-[variable(X), variable(Y)], X-Y-Z-W-[variable(Z), variable(Y)],
         X-Y-Z-W-[variable(X), variable(W)], X-Y-Z-W-[variable(Z), variable(W)]].

test('terms_int_int_intersection_?_?_?_?_x==w', [ fail ]) :-
  clp_term:terms_intersection_int_int([variable(X), variable(_)], [variable(_), variable(W)], singleton(variable(X))),
  \+ X == W.

test('terms_int_int_intersection_?_?_?_?_y==z', [ fail ]) :-
  clp_term:terms_intersection_int_int([variable(_), variable(Y)], [variable(Z), variable(_)], singleton(variable(Y))),
  \+ Y == Z.

test('terms_int_int_intersection_y==z_shortcuts_to_singleton') :-
  Y = Z,
  setof(Y-Z-I, clp_term:terms_intersection_int_int([variable(_), variable(Y)], [variable(Z), variable(_)], I), Ans),
  Ans = [Y-Z-singleton(variable(Y))].

test('terms_int_int_intersection_x==w_shortcuts_to_singleton') :-
  X = W,
  setof(X-W-I, clp_term:terms_intersection_int_int([variable(X), variable(_)], [variable(_), variable(W)], I), Ans),
  Ans = [X-W-singleton(variable(X))].


% Tests for terms_dom_intersection/3
test('terms_dom_intersection_allterms_allterms') :-
  terms_dom_intersection(all_terms, all_terms, all_terms).

test('terms_dom_intersection_allterms_singleton') :-
  terms_dom_intersection(all_terms, singleton(variable(X)), singleton(variable(X))).

test('terms_dom_intersection_allterms_termsfrom') :-
  terms_dom_intersection(all_terms, terms_from(variable(X)), terms_from(variable(X))).

test('terms_dom_intersection_allterms_termsto') :-
  terms_dom_intersection(all_terms, terms_to(variable(X)), terms_to(variable(X))).

test('terms_dom_intersection_allterms_int') :-
  terms_dom_intersection(all_terms, [variable(X),variable(Y)], [variable(X),variable(Y)]).

test('terms_dom_intersection_termsfrom_allterms') :-
  terms_dom_intersection(terms_from(variable(X)), all_terms, terms_from(variable(X))).

test('terms_dom_intersection_termsfrom_singleton_c_c') :-
  terms_dom_intersection(terms_from(const(1)), singleton(const(2)), singleton(const(2))).

test('terms_dom_intersection_termsfrom_singleton_c_v') :-
  setof(X-I, terms_dom_intersection(terms_from(const(1)), singleton(variable(X)), I), Ans),
  Ans = [X-empty, X-singleton(variable(X))].

test('terms_dom_intersection_termsfrom_singleton_v_c') :-
  setof(I, terms_dom_intersection(terms_from(variable(_)), singleton(const(2)), I), Ans),
  Ans = [empty, singleton(const(2))].

test('terms_dom_intersection_termsfrom_singleton_v_v') :-
  setof(Y-I, terms_dom_intersection(terms_from(variable(_)), singleton(variable(Y)), I), Ans),
  Ans = [Y-empty, Y-singleton(variable(Y))].

test('terms_dom_intersection_termsfrom_termsfrom') :-
  setof(X-Y-FromFrom1, terms_dom_intersection(terms_from(variable(X)), terms_from(variable(Y)), FromFrom1), FromFrom1s),
  setof(X-Y-FromFrom2, clp_term:terms_intersection_from_from(terms_from(variable(X)), terms_from(variable(Y)), FromFrom2), FromFrom1s).

test('terms_dom_intersection_termsfrom_termsto') :-
  setof(X-Y-FromTo1, terms_dom_intersection(terms_from(variable(X)), terms_to(variable(Y)), FromTo1), FromTo1s),
  setof(X-Y-FromTo2, clp_term:terms_intersection_from_to(terms_from(variable(X)), terms_to(variable(Y)), FromTo2), FromTo1s).

test('terms_dom_intersection_termsfrom_int') :-
  setof(X-Y-Z-FromInt1, terms_dom_intersection(terms_from(variable(X)), [variable(Y),variable(Z)], FromInt1), FromInt1s),
  setof(X-Y-Z-FromInt2, clp_term:terms_intersection_from_int(terms_from(variable(X)), [variable(Y),variable(Z)], FromInt2), FromInt1s).

test('terms_dom_intersection_termsto_allterms') :-
  terms_dom_intersection(terms_to(variable(X)), all_terms, terms_to(variable(X))).

test('terms_dom_intersection_termsto_singleton_c_c') :-
  terms_dom_intersection(terms_to(const(2)), singleton(const(1)), singleton(const(1))).

test('terms_dom_intersection_termsto_singleton_c_v') :-
  setof(X-I, terms_dom_intersection(terms_to(const(1)), singleton(variable(X)), I), Ans),
  Ans = [X-empty, X-singleton(variable(X))].

test('terms_dom_intersection_termsto_singleton_v_c') :-
  setof(I, terms_dom_intersection(terms_to(variable(_)), singleton(const(1)), I), Ans),
  Ans = [empty, singleton(const(1))].

test('terms_dom_intersection_termsto_singleton_v_v') :-
  setof(I, terms_dom_intersection(terms_to(variable(_)), singleton(variable(Y)), I), Ans),
  Ans = [empty, singleton(variable(Y))].

test('terms_dom_intersection_termsto_termsfrom') :-
  setof(X-Y-ToFrom1, terms_dom_intersection(terms_to(variable(X)), terms_from(variable(Y)), ToFrom1), ToFrom1s),
  setof(X-Y-ToFrom2, clp_term:terms_intersection_to_from(terms_to(variable(X)), terms_from(variable(Y)), ToFrom2), ToFrom1s).

test('terms_dom_intersection_termsto_termsto') :-
  setof(X-Y-ToTo1, terms_dom_intersection(terms_to(variable(X)), terms_to(variable(Y)), ToTo1), ToTo1s),
  setof(X-Y-ToTo2, clp_term:terms_intersection_to_to(terms_to(variable(X)), terms_to(variable(Y)), ToTo2), ToTo1s).

test('terms_dom_intersection_termsto_int') :-
  setof(X-Y-Z-ToInt1, terms_dom_intersection(terms_to(variable(X)), [variable(Y),variable(Z)], ToInt1), ToInt1s),
  setof(X-Y-Z-ToInt2, clp_term:terms_intersection_to_int(terms_to(variable(X)), [variable(Y),variable(Z)], ToInt2), ToInt1s).

test('terms_dom_intersection_int_allterms') :-
  terms_dom_intersection([variable(X),variable(Y)], all_terms, [variable(X),variable(Y)]).

test('terms_dom_intersection_int_singleton_[c,c]_c') :-
  terms_dom_intersection([const(1), const(3)], singleton(const(2)), singleton(const(2))).

test('terms_dom_intersection_int_singleton_[c,c]_v') :-
  setof(Z-I, terms_dom_intersection([const(1), const(3)], singleton(variable(Z)), I), Ans),
  Ans = [Z-empty, Z-singleton(variable(Z))].

test('terms_dom_intersection_int_singleton_[c,v]_c') :-
  setof(I, terms_dom_intersection([const(1), variable(_)], singleton(const(3)), I), Ans),
  Ans = [empty, singleton(const(3))].

test('terms_dom_intersection_int_singleton_[c,v]_v') :-
  setof(Z-I, terms_dom_intersection([const(1), variable(_)], singleton(variable(Z)), I), Ans),
  Ans = [Z-empty, Z-singleton(variable(Z))].

test('terms_dom_intersection_int_singleton_[v,c]_c') :-
  setof(I, terms_dom_intersection([variable(_), const(3)], singleton(const(1)), I), Ans),
  Ans = [empty, singleton(const(1))].

test('terms_dom_intersection_int_singleton_[v,c]_v') :-
  setof(Z-I, terms_dom_intersection([variable(_), const(3)], singleton(variable(Z)), I), Ans),
  Ans = [Z-empty, Z-singleton(variable(Z))].

test('terms_dom_intersection_int_singleton_[v,v]_c') :-
  setof(I, terms_dom_intersection([variable(_), variable(_)], singleton(const(2)), I), Ans),
  Ans = [empty, singleton(const(2))].

test('terms_dom_intersection_int_singleton_[v,v]_v') :-
  setof(Z-I, terms_dom_intersection([variable(_), variable(_)], singleton(variable(Z)), I), Ans),
  Ans = [Z-empty, Z-singleton(variable(Z))].

test('terms_dom_intersection_int_termsfrom') :-
  setof(X-Y-Z-IntFrom1, terms_dom_intersection([variable(X),variable(Y)], terms_from(variable(Z)), IntFrom1), IntFrom1s),
  setof(X-Y-Z-IntFrom2, clp_term:terms_intersection_from_int(terms_from(variable(Z)), [variable(X),variable(Y)], IntFrom2), IntFrom1s).

test('terms_dom_intersection_int_termsto') :-
  setof(X-Y-Z-IntTo1, terms_dom_intersection([variable(X),variable(Y)], terms_to(variable(Z)), IntTo1), IntTo1s),
  setof(X-Y-Z-IntTo2, clp_term:terms_intersection_to_int(terms_to(variable(Z)), [variable(X),variable(Y)], IntTo2), IntTo1s).

test('terms_dom_intersection_int_int') :-
  setof(X-Y-Z-W-IntInt1, terms_dom_intersection([variable(X),variable(Y)], [variable(Z),variable(W)], IntInt1), IntInt1s),
  setof(X-Y-Z-W-IntInt2, clp_term:terms_intersection_int_int([variable(X),variable(Y)], [variable(Z),variable(W)], IntInt2), IntInt1s).

test('terms_dom_intersection_singleton_allterms') :-
  terms_dom_intersection(singleton(variable(X)), all_terms, singleton(variable(X))).

test('terms_dom_intersection_singleton_singleton_c_c') :-
  terms_dom_intersection(singleton(const(1)), singleton(const(1)), singleton(const(1))).

test('terms_dom_intersection_singleton_singleton_c_v') :-
  setof(Y-I, terms_dom_intersection(singleton(const(1)), singleton(variable(Y)), I), Ans),
  Ans = [Y-empty, Y-singleton(const(1))].

test('terms_dom_intersection_singleton_singleton_c_v_unifies') :-
  setof(Y, terms_dom_intersection(singleton(const(1)), singleton(variable(Y)), singleton(const(1))), [Y1]),
  Y1 == 1.

test('terms_dom_intersection_singleton_singleton_v_c') :-
  setof(X-I, terms_dom_intersection(singleton(variable(X)), singleton(const(1)), I), Ans),
  Ans = [X-empty, X-singleton(const(1))].

test('terms_dom_intersection_singleton_singleton_v_c_unifies') :-
  setof(X, terms_dom_intersection(singleton(variable(X)), singleton(const(1)), singleton(const(1))), [X1]),
  X1 == 1.

test('terms_dom_intersection_singleton_singleton_v_v') :-
  setof(X-I, terms_dom_intersection(singleton(variable(X)), singleton(variable(_)), I), Ans),
  Ans = [X-singleton(variable(X)), X-empty].

test('terms_dom_intersection_singleton_singleton_v_v_unifies') :-
  setof(X-Y, terms_dom_intersection(singleton(variable(X)), singleton(variable(Y)), singleton(variable(X))), [X1-Y1]),
  X1 == Y1.

test('terms_dom_intersection_singleton_termsfrom_c_c') :-
  terms_dom_intersection(singleton(const(2)), terms_from(const(1)), Intersection),
  terms_dom_intersection(terms_from(const(1)), singleton(const(2)), Intersection).

test('terms_dom_intersection_singleton_termsfrom_c_v') :-
  setof(Y-SFrom1, terms_dom_intersection(singleton(const(2)), terms_from(variable(Y)), SFrom1), SFrom1s),
  setof(Y-SFrom2, terms_dom_intersection(terms_from(variable(Y)), singleton(const(2)), SFrom2), SFrom1s).

test('terms_dom_intersection_singleton_termsfrom_v_c') :-
  setof(X-SFrom1, terms_dom_intersection(singleton(variable(X)), terms_from(const(1)), SFrom1), SFrom1s),
  setof(X-SFrom2, terms_dom_intersection(terms_from(const(1)), singleton(variable(X)), SFrom2), SFrom1s).

test('terms_dom_intersection_singleton_termsfrom_v_v') :-
  setof(X-Y-SFrom1, terms_dom_intersection(singleton(variable(X)), terms_from(variable(Y)), SFrom1), SFrom1s),
  setof(X-Y-SFrom2, terms_dom_intersection(terms_from(variable(Y)), singleton(variable(X)), SFrom2), SFrom1s).

test('terms_dom_intersection_singleton_termsto_c_c') :-
  terms_dom_intersection(singleton(const(1)), terms_to(const(2)), Intersection),
  terms_dom_intersection(terms_to(const(2)), singleton(const(1)), Intersection).

test('terms_dom_intersection_singleton_termsto_c_v') :-
  setof(Y-STo1, terms_dom_intersection(singleton(const(1)), terms_to(variable(Y)), STo1), STo1s),
  setof(Y-STo2, terms_dom_intersection(terms_to(variable(Y)), singleton(const(1)), STo2), STo1s).

test('terms_dom_intersection_singleton_termsto_v_c') :-
  setof(X-STo1, terms_dom_intersection(singleton(variable(X)), terms_to(const(2)), STo1), STo1s),
  setof(X-STo2, terms_dom_intersection(terms_to(const(2)), singleton(variable(X)), STo2), STo1s).

test('terms_dom_intersection_singleton_termsto_v_v') :-
  setof(X-Y-STo1, terms_dom_intersection(singleton(variable(X)), terms_to(variable(Y)), STo1), STo1s),
  setof(X-Y-STo2, terms_dom_intersection(terms_to(variable(Y)), singleton(variable(X)), STo2), STo1s).

test('terms_dom_intersection_singleton_int_c_[c,c]') :-
  terms_dom_intersection(singleton(const(2)), [const(1), const(3)], Intersection),
  terms_dom_intersection([const(1), const(3)], singleton(const(2)), Intersection).

test('terms_dom_intersection_singleton_int_c_[c,v]') :-
  setof(Z-SInt1, terms_dom_intersection(singleton(const(2)), [const(1), variable(Z)], SInt1), SInt1s),
  setof(Z-SInt2, terms_dom_intersection([const(1), variable(Z)], singleton(const(2)), SInt2), SInt1s).

test('terms_dom_intersection_singleton_int_c_[v,c]') :-
  setof(Y-SInt1, terms_dom_intersection(singleton(const(2)), [variable(Y), const(3)], SInt1), SInt1s),
  setof(Y-SInt2, terms_dom_intersection([variable(Y), const(3)], singleton(const(2)), SInt2), SInt1s).

test('terms_dom_intersection_singleton_int_c_[v,v]') :-
  setof(Y-Z-SInt1, terms_dom_intersection(singleton(const(2)), [variable(Y), variable(Z)], SInt1), SInt1s),
  setof(Y-Z-SInt2, terms_dom_intersection([variable(Y), variable(Z)], singleton(const(2)), SInt2), SInt1s).

test('terms_dom_intersection_singleton_int_v_[c,c]') :-
  setof(X-SInt1, terms_dom_intersection(singleton(variable(X)), [const(1), const(3)], SInt1), SInt1s),
  setof(X-SInt2, terms_dom_intersection([const(1), const(3)], singleton(variable(X)), SInt2), SInt1s).

test('terms_dom_intersection_singleton_int_v_[c,v]') :-
  setof(X-Z-SInt1, terms_dom_intersection(singleton(variable(X)), [const(1), variable(Z)], SInt1), SInt1s),
  setof(X-Z-SInt2, terms_dom_intersection([const(1), variable(Z)], singleton(variable(X)), SInt2), SInt1s).

test('terms_dom_intersection_singleton_int_v_[v,c]') :-
  setof(X-Y-SInt1, terms_dom_intersection(singleton(variable(X)), [variable(Y), const(3)], SInt1), SInt1s),
  setof(X-Y-SInt2, terms_dom_intersection([variable(Y), const(3)], singleton(variable(X)), SInt2), SInt1s).

test('terms_dom_intersection_singleton_int_v_[v,v]') :-
  setof(X-Y-Z-SInt1, terms_dom_intersection(singleton(variable(X)), [variable(Y), variable(Z)], SInt1), SInt1s),
  setof(X-Y-Z-SInt2, terms_dom_intersection([variable(Y), variable(Z)], singleton(variable(X)), SInt2), SInt1s).

test('terms_dom_intersection_normalizes_allterms_singleton') :-
  X = 42,
  terms_dom_intersection(all_terms, singleton(variable(X)), singleton(const(42))).

test('terms_dom_intersection_normalizes_allterms_termsfrom') :-
  X = 42,
  terms_dom_intersection(all_terms, terms_from(variable(X)), terms_from(const(X))).

test('terms_dom_intersection_normalizes_allterms_termsto') :-
  X = 42,
  terms_dom_intersection(all_terms, terms_to(variable(X)), terms_to(const(X))).

test('terms_dom_intersection_normalizes_allterms_int') :-
  X = 42, Y = 43,
  terms_dom_intersection(all_terms, [variable(X), variable(Y)], [const(X), const(Y)]).

test('terms_dom_intersection_normalizes_termsfrom_allterms') :-
  X = 42,
  terms_dom_intersection(terms_from(variable(X)), all_terms, terms_from(const(X))).

test('terms_dom_intersection_normalizes_termsfrom_singleton') :-
  X = 42, Y = 43,
  terms_dom_intersection(terms_from(variable(X)), singleton(variable(Y)), singleton(const(Y))).

test('terms_dom_intersection_normalizes_termsfrom_termsfrom') :-
  X = 42, Y = 43,
  setof(I, terms_dom_intersection(terms_from(variable(X)), terms_from(variable(Y)), I), [terms_from(const(Y))]).

test('terms_dom_intersection_normalizes_termsfrom_termsto') :-
  X = 42, Y = 43,
  setof(I, terms_dom_intersection(terms_from(variable(X)), terms_to(variable(Y)), I), [[const(X), const(Y)]]).

test('terms_dom_intersection_normalizes_termsfrom_int') :-
  X = 42, Y = 43, Z = 44,
  terms_dom_intersection(terms_from(variable(X)), [variable(Y), variable(Z)], [const(Y), const(Z)]).

test('terms_dom_intersection_normalizes_termsto_allterms') :-
  X = 42,
  terms_dom_intersection(terms_to(variable(X)), all_terms, terms_to(const(X))).

test('terms_dom_intersection_normalizes_termsto_singleton') :-
  X = 43, Y = 42,
  terms_dom_intersection(terms_to(variable(X)), singleton(variable(Y)), singleton(const(Y))).

test('terms_dom_intersection_normalizes_termsto_termsfrom') :-
  X = 43, Y = 42,
  setof(I, terms_dom_intersection(terms_to(variable(X)), terms_from(variable(Y)), I), [[const(Y), const(X)]]).

test('terms_dom_intersection_normalizes_termsto_termsto') :-
  X = 42, Y = 43,
  setof(I, terms_dom_intersection(terms_to(variable(X)), terms_to(variable(Y)), I), [terms_to(const(X))]).

test('terms_dom_intersection_normalizes_termsto_int') :-
  X = 44, Y = 42, Z = 43,
  terms_dom_intersection(terms_to(variable(X)), [variable(Y), variable(Z)], [const(Y), const(Z)]).

test('terms_dom_intersection_normalizes_int_allterms') :-
  X = 42, Y = 43,
  terms_dom_intersection([variable(X), variable(Y)], all_terms, [const(X), const(Y)]).

test('terms_dom_intersection_normalizes_int_singleton') :-
  X = 41, Y = 43, Z = 42,
  terms_dom_intersection([variable(X), variable(Y)], singleton(variable(Z)), singleton(const(Z))).

test('terms_dom_intersection_normalizes_int_termsfrom') :-
  X = 42, Y = 43, Z = 41,
  setof(I, terms_dom_intersection([variable(X), variable(Y)], terms_from(variable(Z)), I), [[const(X), const(Y)]]).

test('terms_dom_intersection_normalizes_int_termsto') :-
  X = 42, Y = 43, Z = 44,
  setof(I, terms_dom_intersection([variable(X), variable(Y)], terms_to(variable(Z)), I), [[const(X), const(Y)]]).

test('terms_dom_intersection_normalizes_int_int') :-
  X = 42, Y = 44, Z = 43, W = 45,
  terms_dom_intersection([variable(X), variable(Y)], [variable(Z), variable(W)], [const(Z), const(Y)]).

test('terms_dom_intersection_normalizes_singleton_allterms') :-
  X = 42,
  terms_dom_intersection(singleton(variable(X)), all_terms, singleton(const(X))).

test('terms_dom_intersection_normalizes_singleton_singleton') :-
  X = 42, Y = 42,
  terms_dom_intersection(singleton(variable(X)), singleton(variable(Y)), singleton(const(X))).

test('terms_dom_intersection_normalizes_singleton_termsfrom') :-
  X = 42, Y = 41,
  terms_dom_intersection(singleton(variable(X)), terms_from(variable(Y)), singleton(const(X))).

test('terms_dom_intersection_normalizes_singleton_termsto') :-
  X = 42, Y = 43,
  terms_dom_intersection(singleton(variable(X)), terms_to(variable(Y)), singleton(const(X))).

test('terms_dom_intersection_normalizes_singleton_int') :-
  X = 42, Y = 41, Z = 43,
  terms_dom_intersection(singleton(variable(X)), [variable(Y), variable(Z)], singleton(const(X))).

test('terms_dom_intersection_uninst_1st', [ fail ]) :-
  terms_dom_intersection(_, terms_from(variable(_)), terms_from(variable(_))).

test('terms_dom_intersection_uninst_2nd', [ fail ]) :-
  terms_dom_intersection(terms_from(variable(_)), _, terms_from(variable(_))).

test('terms_dom_intersection_1st_uninst_endpoint', [ throws(error(instantiation_error(X), _)) ]) :-
  terms_dom_intersection(terms_from(X), terms_from(variable(_)), terms_from(variable(_))).

test('terms_dom_intersection_2nd_uninst_endpoint', [ throws(error(instantiation_error(Y), _)) ]) :-
  terms_dom_intersection(terms_from(variable(_)), terms_from(Y), terms_from(variable(_))).


% Tests for the unification hook
test('unify_empty_intersection_fails_to_unify', [ fail ]) :-
  term_at_least(X, 2),
  term_at_most(Y, 1),
  X = Y.

test('unify_singleton_intersection_sets_exact_value_and_removes_attributes_c', [ fail ]) :-
  term_at_least(X, 2),
  term_at_most(Y, 2),
  X = Y,
  (X \== 2 ; Y \== 2 ; get_attr(X, clp_term, _) ; get_attr(Y, clp_term, _)).

test('unify_singleton_intersection2_sets_exact_value_and_removes_attributes_c', [ fail ]) :-
  clp_term:term_indomain(X, [const(1), const(2)]),
  clp_term:term_indomain(Y, [const(2), const(3)]),
  X = Y,
  (X \== 2 ; Y \== 2 ; get_attr(X, clp_term, _) ; get_attr(Y, clp_term, _)).

test('unify_singleton_intersection_sets_exact_value_and_removes_attributes_v', [ fail ]) :-
  term_at_least(X, Z),
  term_at_most(Y, Z),
  X = Y,
  (X \== Z ; Y \== Z ; get_attr(X, clp_term, _) ; get_attr(Y, clp_term, _)).

test('unify_singleton_intersection2_sets_exact_value_and_removes_attributes_v', [ fail ]) :-
  clp_term:term_indomain(X, [const(1), variable(Z)]),
  clp_term:term_indomain(Y, [variable(Z), const(3)]),
  X = Y,
  (X \== Z ; Y \== Z ; get_attr(X, clp_term, _) ; get_attr(Y, clp_term, _)).

test('unify_allterms_allterms', [ fail ]) :-
  clp_term:is_term(X),
  clp_term:is_term(Y),
  X = Y,
  \+ (get_attr(X, clp_term, all_terms), get_attr(Y, clp_term, all_terms)).

test('unify_allterms_termsfrom_c', [ fail ]) :-
  clp_term:is_term(X),
  term_at_least(Y, 1),
  X = Y,
  \+ get_attr(X, clp_term, terms_from(const(1))).

test('unify_allterms_termsfrom_v', [ fail ]) :-
  clp_term:is_term(X),
  term_at_least(Y, Z),
  X = Y,
  \+ get_attr(X, clp_term, terms_from(variable(Z))).

test('unify_allterms_termsto_c', [ fail ]) :-
  clp_term:is_term(X),
  term_at_most(Y, 1),
  X = Y,
  \+ get_attr(X, clp_term, terms_to(const(1))).

test('unify_allterms_termsto_v', [ fail ]) :-
  clp_term:is_term(X),
  term_at_most(Y, Z),
  X = Y,
  \+ get_attr(X, clp_term, terms_to(variable(Z))).

test('unify_allterms_int_c_c', [ fail ]) :-
  clp_term:is_term(X),
  term_at_least(Y, 1), term_at_most(Y, 2),
  X = Y,
  \+ get_attr(X, clp_term, [const(1), const(2)]).

test('unify_allterms_int_c_v', [ fail ]) :-
  clp_term:is_term(X),
  term_at_least(Y, 1), term_at_most(Y, U), dif(1, U),
  X = Y,
  \+ get_attr(X, clp_term, [const(1), variable(U)]).

test('unify_allterms_int_v_c', [ fail ]) :-
  clp_term:is_term(X),
  term_at_least(Y, L), term_at_most(Y, 2), dif(L, 2),
  X = Y,
  \+ get_attr(X, clp_term, [variable(L), const(2)]).

test('unify_allterms_int_v_v', [ fail ]) :-
  clp_term:is_term(X),
  term_at_least(Y, L), term_at_most(Y, U), dif(L, U),
  X = Y,
  \+ get_attr(X, clp_term, [variable(L), variable(U)]).

test('unify_termsfrom_allterms', [ fail ]) :-
  term_at_least(X, 1),
  clp_term:is_term(Y),
  X = Y,
  \+ get_attr(Y, clp_term, terms_from(const(1))).

test('unify_termsfrom_termsfrom_c_c', [ fail ]) :-
  term_at_least(X, 1),
  term_at_least(Y, 2),
  X = Y,
  \+ get_attr(Y, clp_term, terms_from(const(2))).

test('unify_termsfrom_termsfrom_c_v', [ fail ]) :-
  term_at_least(X, 1),
  term_at_least(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_from_from(Dom1, Dom2, Expected)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_termsfrom_termsfrom_v_c', [ fail ]) :-
  term_at_least(X, _),
  term_at_least(Y, 2),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, clp_term:terms_intersection_from_from(Dom1, Dom2, Expected), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_termsfrom_termsfrom_v_v', [ fail ]) :-
  term_at_least(X, _),
  term_at_least(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, clp_term:terms_intersection_from_from(Dom1, Dom2, Expected), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_termsfrom_termsto_c_c', [ fail ]) :-
  term_at_least(X, 1),
  term_at_most(Y, 2),
  X = Y,
  \+ get_attr(Y, clp_term, [const(1), const(2)]).

test('unify_termsfrom_termsto_c_v', [ fail ]) :-
  term_at_least(X, 1),
  term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_from_to(Dom1, Dom2, Expected),
                   \+ Expected == empty, \+ Expected = singleton(_)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  Expecteds = [_-_-Es], Actuals = [_-_-As],
  \+ Es = As.

test('unify_termsfrom_termsto_c_v_singleton', [ fail ]) :-
  term_at_least(X, 1),
  term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_from_to(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_termsfrom_termsto_v_c', [ fail ]) :-
  term_at_least(X, _),
  term_at_most(Y, 2),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_from_to(Dom1, Dom2, Expected),
        \+ Expected == empty, \+ Expected = singleton(_)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsfrom_termsto_v_c_singleton', [ fail ]) :-
  term_at_least(X, _),
  term_at_most(Y, 2),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_from_to(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_termsfrom_termsto_v_v', [ fail ]) :-
  term_at_least(X, _),
  term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_from_to(Dom1, Dom2, Expected),
        \+ Expected == empty, \+ Expected = singleton(_)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsfrom_termsto_v_v_singleton', [ fail ]) :-
  term_at_least(X, _),
  term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_from_to(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_termsfrom_int_c_[c,c]', [ fail ]) :-
  term_at_least(X, 2),
  term_at_least(Y, 1), term_at_most(Y, 3),
  X = Y,
  \+ get_attr(X, clp_term, [const(2), const(3)]).

test('unify_termsfrom_int_c_[c,v]', [ fail ]) :-
  term_at_least(X, 2),
  term_at_least(Y, 1), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_from_int(Dom1, Dom2, Expected),
                       \+ Expected == empty, \+ Expected = singleton(_)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  Expecteds = [_-_-Es], Actuals = [_-_-As],
  \+ Es = As.

test('unify_termsfrom_int_c_[c,v]_singleton', [ fail ]) :-
  term_at_least(X, 2),
  term_at_least(Y, 1), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_from_int(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_termsfrom_int_c_[v,c]', [ fail ]) :-
  term_at_least(X, 2),
  term_at_least(Y, _), term_at_most(Y, 3),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, clp_term:terms_intersection_from_int(Dom1, Dom2, Expected), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsfrom_int_c_[v,v]', [ fail ]) :-
  term_at_least(X, 2),
  term_at_least(Y, _), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_from_int(Dom1, Dom2, Expected),
                       \+ Expected == empty, \+ Expected = singleton(_)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  Expecteds = [_-_-Es1, _-_-Es2], Actuals = [_-_-As1, _-_-As2],
  (Es1 \= As1 ; Es2 \= As2).

test('unify_termsfrom_int_c_[v,v]_singleton', [ fail ]) :-
  term_at_least(X, 2),
  term_at_least(Y, _), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_from_int(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_termsfrom_int_v_[c,c]', [ fail ]) :-
  term_at_least(X, _),
  term_at_least(Y, 1), term_at_most(Y, 3),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_from_int(Dom1, Dom2, Expected),
        \+ Expected == empty, \+ Expected = singleton(_)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsfrom_int_v_[c,c]_singleton', [ fail ]) :-
  term_at_least(X, _),
  term_at_least(Y, 1), term_at_most(Y, 3),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_from_int(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_termsfrom_int_v_[c,v]', [ fail ]) :-
  term_at_least(X, _),
  term_at_least(Y, 1), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_from_int(Dom1, Dom2, Expected), 
        \+ Expected == empty, \+ Expected = singleton(_)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsfrom_int_v_[c,v]_singleton', [ fail ]) :-
  term_at_least(X, _),
  term_at_least(Y, 1), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_from_int(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_termsfrom_int_v_[v,c]', [ fail ]) :-
  term_at_least(X, _),
  term_at_least(Y, _), term_at_most(Y, 3),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_from_int(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsfrom_int_v_[v,c]_singleton', [ fail ]) :-
  term_at_least(X, _),
  term_at_least(Y, _), term_at_most(Y, 3),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_from_int(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_termsfrom_int_v_[v,v]', [ fail ]) :-
  term_at_least(X, _),
  term_at_least(Y, _), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_from_int(Dom1, Dom2, Expected),
                   \+ Expected == empty, \+ Expected = singleton(_)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsfrom_int_v_[v,v]_singleton', [ fail ]) :-
  term_at_least(X, _),
  term_at_least(Y, _), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_from_int(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_termsto_allterms', [ fail ]) :-
  term_at_most(X, 1),
  clp_term:is_term(Y),
  X = Y,
  \+ get_attr(Y, clp_term, terms_to(const(1))).

test('unify_termsto_termsfrom_c_c', [ fail ]) :-
  term_at_most(X, 2),
  term_at_least(Y, 1),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_to_int(Dom1, Dom2, Expected)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsto_termsfrom_c_v', [ fail ]) :-
  term_at_most(X, 2),
  term_at_least(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_to_from(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsto_termsfrom_c_v_singleton', [ fail ]) :-
  term_at_most(X, 2),
  term_at_least(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_to_from(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_termsto_termsfrom_v_c', [ fail ]) :-
  term_at_most(X, _),
  term_at_least(Y, 1),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_to_from(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  Expecteds = [_-_-Es], Actuals = [_-_-As],
  \+ Es = As.

test('unify_termsto_termsfrom_v_c_singleton', [ fail ]) :-
  term_at_most(X, _),
  term_at_least(Y, 1),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_to_from(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_termsto_termsfrom_v_v', [ fail ]) :-
  term_at_most(X, _),
  term_at_least(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_to_from(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsto_termsfrom_v_v_singleton', [ fail ]) :-
  term_at_most(X, _),
  term_at_least(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_to_from(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_termsto_termsto_c_c', [ fail ]) :-
  term_at_most(X, 1),
  term_at_most(Y, 2),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_to_to(Dom1, Dom2, Expected)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsto_termsto_c_v', [ fail ]) :-
  term_at_most(X, 1),
  term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, clp_term:terms_intersection_to_to(Dom1, Dom2, Expected), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_termsto_termsto_v_c', [ fail ]) :-
  term_at_most(X, _),
  term_at_most(Y, 2),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, clp_term:terms_intersection_to_to(Dom1, Dom2, Expected), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_termsto_termsto_v_v', [ fail ]) :-
  term_at_most(X, _),
  term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, clp_term:terms_intersection_to_to(Dom1, Dom2, Expected), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsto_int_c_[c,c]', [ fail ]) :-
  term_at_most(X, 2),
  term_at_least(Y, 1), term_at_most(Y, 3),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, clp_term:terms_intersection_to_int(Dom1, Dom2, Expected), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsto_int_c_[c,v]', [ fail ]) :-
  term_at_most(X, 2),
  term_at_least(Y, 1), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, clp_term:terms_intersection_to_int(Dom1, Dom2, Expected), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsto_int_c_[v,c]', [ fail ]) :-
  term_at_most(X, 2),
  term_at_least(Y, _), term_at_most(Y, 3),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2), Dom2 = [_,_],
  setof(X-Y-Expected, (clp_term:terms_intersection_to_int(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsto_int_c_[v,c]_singleton', [ fail ]) :-
  term_at_most(X, 2),
  term_at_least(Y, _), term_at_most(Y, 3),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2), Dom2 = [_,_],
  clp_term:terms_intersection_to_int(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_termsto_int_c_[v,v]', [ fail ]) :-
  term_at_most(X, 2), 
  term_at_least(Y, _), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_to_int(Dom1, Dom2, Expected),
                       \+ Expected == empty, \+ Expected = singleton(_)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsto_int_c_[v,v]_singleton', [ fail ]) :-
  term_at_most(X, 2), 
  term_at_least(Y, _), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2), Dom2 = [_,_],
  clp_term:terms_intersection_to_int(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_termsto_int_v_[c,c]', [ fail ]) :-
  term_at_most(X, _),
  term_at_least(Y, 1), term_at_most(Y, 3),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_to_int(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsto_int_v_[c,c]_singleton', [ fail ]) :-
  term_at_most(X, _),
  term_at_least(Y, 1), term_at_most(Y, 3),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_to_int(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_termsto_int_v_[c,v]', [ fail ]) :-
  term_at_most(X, _),
  term_at_least(Y, 1), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_to_int(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsto_int_v_[c,v]_singleton', [ fail ]) :-
  term_at_most(X, _),
  term_at_least(Y, 1), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_to_int(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_termsto_int_v_[v,c]', [ fail ]) :-
  term_at_most(X, _),
  term_at_least(Y, _), term_at_most(Y, 3),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_to_int(Dom1, Dom2, Expected),
                       \+ Expected == empty, \+ Expected = singleton(_)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsto_int_v_[v,c]_singleton', [ fail ]) :-
  term_at_most(X, _),
  term_at_least(Y, _), term_at_most(Y, 3),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_to_int(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_termsto_int_v_[v,v]', [ fail ]) :-
  term_at_most(X, _),
  term_at_least(Y, _), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_to_int(Dom1, Dom2, Expected),
                       \+ Expected == empty, \+ Expected = singleton(_)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_termsto_int_v_[v,v]_singleton', [ fail ]) :-
  term_at_most(X, _),
  term_at_least(Y, _), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_to_int(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_int_allterms_[c,c]', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, 3),
  clp_term:is_term(Y),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (terms_dom_intersection(Dom1, Dom2, Expected)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_int_allterms_[c,v]', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, _),
  clp_term:is_term(Y),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (terms_dom_intersection(Dom1, Dom2, Expected)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_int_allterms_[v,c]', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, 3),
  clp_term:is_term(Y),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (terms_dom_intersection(Dom1, Dom2, Expected)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_int_allterms_[v,v]', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, _),
  clp_term:is_term(Y),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (terms_dom_intersection(Dom1, Dom2, Expected)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_int_termsfrom_[c,c]_c', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, 3),
  term_at_least(Y, 2),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (terms_dom_intersection(Dom1, Dom2, Expected)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_int_termsfrom_[c,c]_v', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, 3),
  term_at_least(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_from(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_int_termsfrom_[c,c]_v_singleton', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, 3),
  term_at_least(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_int_from(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_int_termsfrom_[c,v]_c', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, _),
  term_at_least(Y, 2),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_from(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  Expecteds = [_-_-Es], Actuals = [_-_-As],
  \+ Es = As.

test('unify_int_termsfrom_[c,v]_c_singleton', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, _),
  term_at_least(Y, 2),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_int_from(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_int_termsfrom_[c,v]_v', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, _),
  term_at_least(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_from(Dom1, Dom2, Expected),
                   \+ Expected == empty, \+ Expected = singleton(_)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_int_termsfrom_[c,v]_v_singleton', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, _),
  term_at_least(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_int_from(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_int_termsfrom_[v,c]_c', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, 3),
  term_at_least(Y, 2),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, clp_term:terms_intersection_int_from(Dom1, Dom2, Expected), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_int_termsfrom_[v,c]_v', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, 3),
  term_at_least(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_from(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_int_termsfrom_[v,c]_v_singleton', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, 3),
  term_at_least(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_int_from(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_int_termsfrom_[v,v]_c', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, _),
  term_at_least(Y, 2),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_from(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_int_termsfrom_[v,v]_c_singleton', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, _),
  term_at_least(Y, 2),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_int_from(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_int_termsfrom_[v,v]_v', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, _),
  term_at_least(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_from(Dom1, Dom2, Expected),
                       \+ Expected == empty, \+ Expected = singleton(_)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_int_termsfrom_[v,v]_v_singleton', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, _),
  term_at_least(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_int_from(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_int_termsto_[c,c]_c', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, 3),
  term_at_most(Y, 2),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_to(Dom1, Dom2, Expected)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_int_termsto_[c,c]_v', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, 3),
  term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_to(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_int_termsto_[c,c]_v_singleton', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, 3),
  term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_int_to(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_int_termsto_[c,v]_c', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, _),
  term_at_most(Y, 2),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, clp_term:terms_intersection_int_to(Dom1, Dom2, Expected), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_int_termsto_[c,v]_v', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, _),
  term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_to(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_int_termsto_[c,v]_v_singleton', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, _),
  term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_int_to(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_int_termsto_[v,c]_c', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, 3),
  term_at_most(Y, 2),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_to(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_int_termsto_[v,c]_c_singleton', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, 3),
  term_at_most(Y, 2),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_int_to(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_int_termsto_[v,c]_v', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, 3),
  term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_to(Dom1, Dom2, Expected),
                   \+ Expected == empty, \+ Expected = singleton(_)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_int_termsto_[v,c]_v_singleton', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, 3),
  term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_int_to(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_int_termsto_[v,v]_c', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, _),
  term_at_most(Y, 2),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_to(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_int_termsto_[v,v]_c_singleton', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, _),
  term_at_most(Y, 2),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_int_to(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_int_termsto_[v,v]_v', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, _),
  term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_to(Dom1, Dom2, Expected),
                   \+ Expected == empty, \+ Expected = singleton(_)), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ Expecteds = Actuals.

test('unify_int_termsto_[v,v]_v_singleton', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, _),
  term_at_most(Y, _),
  get_attr(X, clp_term, Dom1),
  get_attr(Y, clp_term, Dom2),
  clp_term:terms_intersection_int_to(Dom1, Dom2, singleton(S)),
  X = Y, \+ get_attr(Y, clp_term, _), arg(1, S, V),
  \+ Y == V.

test('unify_int_int_[c,c]_[c,c]', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, 3),
  term_at_least(Y, 2), term_at_most(Y, 4),
  X = Y,
  \+ get_attr(X, clp_term, [const(2), const(3)]).

test('unify_int_int_[c,c]_[c,v]', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, 3),
  term_at_least(Y, 2), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1), get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, clp_term:terms_intersection_int_int(Dom1, Dom2, Expected), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_int_int_[c,c]_[v,c]', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, 3),
  term_at_least(Y, _), term_at_most(Y, 4),
  get_attr(X, clp_term, Dom1), get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_int(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_int_int_[c,c]_[v,v]', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, 3),
  term_at_least(Y, _), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1), get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_int(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_int_int_[c,v]_[c,c]', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, _),
  term_at_least(Y, 2), term_at_most(Y, 4),
  get_attr(X, clp_term, Dom1), get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_int(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_int_int_[c,v]_[c,v]', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, _),
  term_at_least(Y, 2), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1), get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_int(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_int_int_[c,v]_[v,c]', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, _),
  term_at_least(Y, _), term_at_most(Y, 4),
  get_attr(X, clp_term, Dom1), get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_int(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_int_int_[c,v]_[v,v]', [ fail ]) :-
  term_at_least(X, 1), term_at_most(X, _),
  term_at_least(Y, _), term_at_most(Y, 4),
  get_attr(X, clp_term, Dom1), get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_int(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_int_int_[v,c]_[c,c]', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, 3),
  term_at_least(Y, 2), term_at_most(Y, 4),
  get_attr(X, clp_term, Dom1), get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_int(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_int_int_[v,c]_[c,v]', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, 3),
  term_at_least(Y, 2), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1), get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_int(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_int_int_[v,c]_[v,c]', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, 3),
  term_at_least(Y, _), term_at_most(Y, 4),
  get_attr(X, clp_term, Dom1), get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_int(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_int_int_[v,c]_[v,v]', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, 3),
  term_at_least(Y, _), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1), get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_int(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_int_int_[v,v]_[c,c]', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, _),
  term_at_least(Y, 2), term_at_most(Y, 4),
  get_attr(X, clp_term, Dom1), get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_int(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_int_int_[v,v]_[c,v]', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, _),
  term_at_least(Y, 2), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1), get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_int(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_int_int_[v,v]_[v,c]', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, _),
  term_at_least(Y, _), term_at_most(Y, 4),
  get_attr(X, clp_term, Dom1), get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_int(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_int_int_[v,v]_[v,v]', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, _),
  term_at_least(Y, _), term_at_most(Y, _),
  get_attr(X, clp_term, Dom1), get_attr(Y, clp_term, Dom2),
  setof(X-Y-Expected, (clp_term:terms_intersection_int_int(Dom1, Dom2, Expected), \+ Expected == empty), Expecteds),
  setof(X-Y-Actual, (X = Y, get_attr(Y, clp_term, Actual)), Actuals),
  \+ (subset(Expecteds, Actuals), subset(Actuals, Expecteds)).

test('unify_attr_free_sets_domain', [ fail ]) :-
  term_at_least(X, 2), term_at_most(X, 4),
  setof(X-Y-Dom, (X = Y, get_attr(Y, clp_term, Dom)), Actuals),
  \+ Actuals = [X-Y-[const(2), const(4)]].

test('unify_free_attr_sets_domain', [ fail ]) :-
  term_at_least(X, 2), term_at_most(X, 4),
  setof(X-Y-Dom, (Y = X, get_attr(Y, clp_term, Dom)), Actuals),
  \+ Actuals = [X-Y-[const(2), const(4)]].

test('unify_allterms_unifies_with_any') :-
  clp_term:is_term(X),
  X = a.

test('unify_termsfrom_const_unifies_indomain') :-
  term_at_least(X, 2),
  X = 3.

test('unify_termsfrom_const_unifies_outdomain', [ fail ]) :-
  term_at_least(X, 2),
  X = 1.

test('unify_termsfrom_var_unifies_indomain') :-
  term_at_least(X, Z),
  X = 3,
  get_attr(Z, clp_term, Dom),
  Dom == terms_to(const(3)).

test('unify_termsto_const_unifies_indomain') :-
  term_at_most(Y, 2),
  Y = 1.

test('unify_termsto_const_unifies_outdomain', [ fail ]) :-
  term_at_most(Y, 2),
  Y = 3.

test('unify_termsto_var_unifies_indomain') :-
  term_at_most(Y, Z),
  Y = 3,
  get_attr(Z, clp_term, Dom),
  Dom == terms_from(const(3)).

test('unify_int_[c,c]_unifies_indomain') :-
  term_at_least(X, 2), term_at_most(X, 4),
  X = 3.

test('unify_int_[c,c]_unifies_outdomain', [ fail ]) :-
  term_at_least(X, 2), term_at_most(X, 4),
  X = 1.

test('unify_int_[c,v]_unifies_indomain', [ fail ]) :-
  term_at_least(X, 2), term_at_most(X, Z),
  X = 3,
  \+ term_at_least(Z, 3).

test('unify_int_[c,v]_unifies_outdomain', [ fail ]) :-
  term_at_least(X, 2), term_at_most(X, _),
  X = 1.

test('unify_int_[v,c]_unifies_indomain', [ fail ]) :-
  term_at_least(X, Z), term_at_most(X, 4),
  X = 3,
  \+ term_at_most(Z, 3).

test('unify_int_[v,c]_unifies_outdomain', [ fail ]) :-
  term_at_least(X, _), term_at_most(X, 4),
  X = 5.

test('unify_int_[v,v]_unifies_indomain', [ fail ]) :-
  term_at_least(X, Z1), term_at_most(X, Z2),
  X = 3,
  \+ term_at_most(Z1, 3), term_at_least(Z2, 3).


% Tests for attribute_termorder_goals/3
test('attribute_termorder_goals_from_c') :-
  clp_term:attribute_termorder_goals(Term, terms_from(const(1)), ResidualGoals),
  ResidualGoals == [term_at_least(Term, 1)].

test('attribute_termorder_goals_from_v') :-
  clp_term:attribute_termorder_goals(Term, terms_from(variable(X)), ResidualGoals),
  ResidualGoals == [term_at_least(Term, X)].

test('attribute_termorder_goals_to_c') :-
  clp_term:attribute_termorder_goals(Term, terms_to(const(2)), ResidualGoals),
  ResidualGoals == [term_at_most(Term, 2)].

test('attribute_termorder_goals_to_v') :-
  clp_term:attribute_termorder_goals(Term, terms_to(variable(Y)), ResidualGoals),
  ResidualGoals == [term_at_most(Term, Y)].

test('attribute_termorder_goals_int_c_c') :-
  clp_term:attribute_termorder_goals(Term, [const(1), const(2)], ResidualGoals),
  ResidualGoals == [term_at_least(Term, 1), term_at_most(Term, 2)].

test('attribute_termorder_goals_int_c_v') :-
  clp_term:attribute_termorder_goals(Term, [const(1), variable(Y)], ResidualGoals),
  ResidualGoals == [term_at_least(Term, 1), term_at_most(Term, Y)].

test('attribute_termorder_goals_int_v_c') :-
  clp_term:attribute_termorder_goals(Term, [variable(X), const(2)], ResidualGoals),
  ResidualGoals == [term_at_least(Term, X), term_at_most(Term, 2)].

test('attribute_termorder_goals_int_v_v') :-
  clp_term:attribute_termorder_goals(Term, [variable(X), variable(Y)], ResidualGoals),
  ResidualGoals == [term_at_least(Term, X), term_at_most(Term, Y)].

:- end_tests(clp_term).

