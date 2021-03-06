:- module(clp_term,
  [ term_at_least/2,
    term_at_most/2,
    is_term/1,
    is_empty_term/1,
    is_singleton_term/2,
    term_indomain/2,
    terms_dom_intersection/3
  ]).

% term_indomain(-Term, +Dom) is det.
% term_indomain(-Term, -Dom) is det.
%
% True whenever the term `Term` belongs to the term order domain `Dom`. If `Term` is already 
% constrained in the standard ordering of terms it is unified with this new constraint.
term_indomain(Term, Dom) :-
  (  nonvar(Term)
  -> throw(error(uninstantiation_error(Term), "Term enumeration is not supported by term_indomain/2"))
  ;  var(Dom)
  -> get_attr(Term, clp_term, Dom)
  ;  (  get_attr(Term, clp_term, Dom1) % already attributed?
     -> terms_dom_intersection(Dom, Dom1, NewDom),
        put_attr(Term, clp_term, NewDom)
     ;  put_attr(Term, clp_term, Dom)
     )
  ).

% is_term(-Term) is det. 
% 
% True whenever `Term` is a term in the standard ordering for terms. If `Term` is already constrained in 
% the standard ordering of terms this new constraint has no effect.
is_term(Term) :-
  term_indomain(Term, all_terms).

% is_empty_term(-Term) is det.
% 
% True whenever `Term` cannot be bound to any value in the standard ordering of terms.
is_empty_term(Term) :-
  term_indomain(Term, empty). 

% is_singleton_term(-Term, +X) is det.
% is_singleton_term(-Term, -X) is det.
%
% True whenever `Term` can only be bound to a single possible value in the standard ordering of terms.
is_singleton_term(Term, X) :-
  (  var(X)
  -> term_indomain(Term, singleton(variable(X)))
  ;  term_indomain(Term, singleton(const(X)))
  ). 

% term_at_least(-Term, +X) is det.
% term_at_least(-Term, -X) is det.
%
% True whenever `Term` is at least as large as `X` in the standard ordering for terms. `X` may be a variable, 
% in which case the resulting half-bounded domain has a variable endpoint that can be instantiated to a 
% constant later. If `Term` is already constrained in the standard ordering of terms it is unified with 
% this new constraint.
term_at_least(Term, X) :-
  (  var(X)
  -> term_indomain(Term, terms_from(variable(X)))
  ;  term_indomain(Term, terms_from(const(X)))
  ).

% term_at_most(-Term, +Y) is det.
% term_at_most(-Term, -Y) is det.
%
% True whenever `Term` is at most as large as `Y` in the standard ordering for terms. `Y` may be a variable, 
% in which case the resulting half-bounded domain has a variable endpoint that can be instantiated to a 
% constant later. If `Term` is already constrained in the standard ordering of terms it is unified with 
% this new constraint.
term_at_most(Term, Y) :-
  (  var(Y)
  -> term_indomain(Term, terms_to(variable(Y)))
  ;  term_indomain(Term, terms_to(const(Y)))
  ).

% term_normalized(+Term0, +Term) is semidet.
% term_normalized(+Term0, -Term) is det.
%
% True whenever `Term` has functor matching `Term0`s current variable status. This helps to ensure correct
% behavior when variable endpoints are grounded. 
term_normalized(Term0, Term) :-
  (  var(Term0)
  -> throw(error(instantiation_error(Term0), "Normalizing uninstantiated terms is not supported in term_normalized/2"))
  ;  Term0 = variable(X)
  -> (  nonvar(X)
     -> Term = const(X)
     ;  Term = Term0
     )
  ;  Term0 = const(_), Term = Term0
  ).

% dom_normalized(+Dom0, +Dom) is semidet.
% dom_normalized(+Dom0, -Dom) is det.
%
% True whenever `Dom` has functors matching `Dom0`s current variable statuses for the relevant
% endpoint variables, where applicable. 
dom_normalized(Dom0, Dom) :-
  nonvar(Dom0),
  (  Dom0 = all_terms 
  -> Dom  = Dom0
  ;  Dom0 = empty
  -> Dom  = Dom0
  ;  Dom0 = terms_from(Term0)
  -> term_normalized(Term0, Term),
     Dom  = terms_from(Term)
  ;  Dom0 = terms_to(Term0)
  -> term_normalized(Term0, Term),
     Dom  = terms_to(Term)
  ;  Dom0 = singleton(Term0)
  -> term_normalized(Term0, Term),
     Dom  = singleton(Term)
  ;  Dom0 = [TermX0, TermY0]
  -> term_normalized(TermX0, TermX),
     term_normalized(TermY0, TermY),
     (  [TermX, TermY] = [const(Same), const(Same)]
     -> Dom = singleton(const(Same))
     ;  [TermX, TermY] = [variable(TermX2), variable(TermY2)], TermX2 == TermY2
     -> Dom = singleton(variable(TermX2))
     ;  Dom  = [TermX, TermY]
     )
  ).

% terms_intersection(terms_from(+X), terms_from(+Y), -Intersection) is multi.
%
% Intersection of two lower-bounded domains. Input domains must be normalized first to yield
% correct answers: see `dom_normalized/2`.
terms_intersection_from_from(terms_from(X), terms_from(Y), Intersection) :-
  (  [X, Y] = [const(X1), const(Y1)] 
  -> (  X1 @>= Y1
     -> Intersection = terms_from(const(X1))
     ;  Intersection = terms_from(const(Y1))
     )
  ;  (  Intersection = terms_from(X) ; Intersection = terms_from(Y) )
  ).

% terms_intersection(terms_to(+X), terms_to(+Y), -Intersection) is multi.
%
% Intersection of two upper-bounded domains. Input domains must be normalized first to yield
% correct answers: see `dom_normalized/2`.
terms_intersection_to_to(terms_to(X), terms_to(Y), Intersection) :-
  (  [X, Y] = [const(X1), const(Y1)] 
  -> (  X1 @=< Y1
     -> Intersection = terms_to(const(X1))
     ;  Intersection = terms_to(const(Y1))
     )
  ;  (  Intersection = terms_to(X) ; Intersection = terms_to(Y) )
  ).

% terms_intersection(terms_from(+X), terms_to(+Y), -Intersection) is multi.
%
% Intersection of a lower-bounded domain with an upper-bounded domain. Input domains must be 
% normalized first to yield correct answers: see `dom_normalized/2`.
terms_intersection_from_to(terms_from(X), terms_to(Y), Intersection) :-
  (  [X, Y] = [const(X1), const(Y1)]
  -> (  X1 == Y1
     -> Intersection = singleton(X)
     ;  X1 @< Y1
     -> Intersection = [X, Y]
     ;  Intersection = empty
     )
  ;  (  X = const(X1)
     -> arg(1, Y, Y1), Y1 = X1, Intersection = singleton(X) 
     ;  X = variable(X1)
     -> arg(1, Y, Y1), X1 = Y1, Intersection = singleton(Y) 
     )
  ;  ( X \== Y, Intersection = [X, Y] )
  ;  Intersection = empty
  ).

% terms_intersection(terms_to(+X), terms_from(+Y), -Intersection) is multi.
%
% Intersection of an upper-bounded domain with a lower-bounded domain. Input domains must be 
% normalized first to yield correct answers: see `dom_normalized/2`.
terms_intersection_to_from(terms_to(X), terms_from(Y), Intersection) :-
  terms_intersection_from_to(terms_from(Y), terms_to(X), Intersection).

% Helper predicate for comparing endpoints
term_order(X, Y, Ord) :-
  (  [X, Y] = [const(X1), const(Y1)]
  -> (  X1 @< Y1
     -> Ord = '<'
     ;  X1 @> Y1
     -> Ord = '>'
     ;  Ord = '='
     )
  ; Ord = '?'
  ).

% Helper predicate for building keys for lookup 
terms_orderKey(X, Y, Z, OrderKey) :-
  term_order(X, Y, XrY),
  term_order(X, Z, XrZ),
  atom_chars(OrderKey, [XrY, XrZ]).

% Lookup table for intersecting half-interval with closed interval 
terms_from_int_lookup(??, X, Y, Z, [[Y,Z], [X,Z], singleton(Z), empty]).
terms_from_int_lookup(?<, X, Y, Z, [[Y,Z], [X,Z]]).
terms_from_int_lookup(?=, _, _, Z, [singleton(Z)]).
terms_from_int_lookup(?>, _, _, _, [empty]).
terms_from_int_lookup(<?, _, Y, Z, [[Y,Z]]).
terms_from_int_lookup(<<, _, Y, Z, [[Y,Z]]).
terms_from_int_lookup(=<, _, Y, Z, [[Y,Z]]).
terms_from_int_lookup(>?, X, _, Z, [[X,Z], singleton(Z), empty]).
terms_from_int_lookup(><, X, _, Z, [[X,Z]]).
terms_from_int_lookup(>=, _, _, Z, [singleton(Z)]).
terms_from_int_lookup(>>, _, _, _, [empty]).

% terms_intersection(terms_from(+X), [+Y, +Z], -Intersection) is multi.
%
% Intersection of a lower-bounded domain with a closed interval. Input domains must be 
% normalized first to yield correct answers: see `dom_normalized/2`.
terms_intersection_from_int(terms_from(X), [Y, Z], Intersection) :-
  terms_orderKey(X, Y, Z, OrderKey),
  terms_from_int_lookup(OrderKey, X, Y, Z, Intersections),
  member(Intersection0, Intersections),
  (  Intersection0 = singleton(Z)
  -> arg(1, X, X1), arg(1, Z, Z1), X1 = Z1, dom_normalized(Intersection0, Intersection)
  ;  Intersection = Intersection0 
  ).

% terms_intersection([+X, +Y], terms_from(+Z), -Intersection) is multi.
%
% Intersection of a closed interval with a lower-bounded domain. Input domains must be 
% normalized first to yield correct answers: see `dom_normalized/2`.
terms_intersection_int_from([X, Y], terms_from(Z), Intersection) :-
  terms_intersection_from_int(terms_from(Z), [X, Y], Intersection).

% Lookup table for intersecting half-interval with closed interval 
terms_to_int_lookup(??, X, Y, Z, [[Y,Z], [Y,X], singleton(Y), empty]).
terms_to_int_lookup(?<, X, Y, _, [[Y,X], singleton(Y), empty]).
terms_to_int_lookup(?=, _, Y, Z, [[Y,Z]]).
terms_to_int_lookup(?>, _, Y, Z, [[Y,Z]]).
terms_to_int_lookup(<?, _, _, _, [empty]).
terms_to_int_lookup(<<, _, _, _, [empty]).
terms_to_int_lookup(=<, _, Y, _, [singleton(Y)]).
terms_to_int_lookup(=?, _, Y, _, [singleton(Y)]).
terms_to_int_lookup(>?, X, Y, Z, [[Y,X], [Y,Z]]).
terms_to_int_lookup(><, X, Y, _, [[Y,X]]).
terms_to_int_lookup(>=, _, Y, Z, [[Y,Z]]).
terms_to_int_lookup(>>, _, Y, Z, [[Y,Z]]).

% terms_intersection(terms_to(+X), [+Y, +Z], -Intersection) is multi.
%
% Intersection of an upper-bounded domain with a closed interval. Input domains must be 
% normalized first to yield correct answers: see `dom_normalized/2`.
terms_intersection_to_int(terms_to(X), [Y, Z], Intersection) :-
  terms_orderKey(X, Y, Z, OrderKey),
  terms_to_int_lookup(OrderKey, X, Y, Z, Intersections),
  member(Intersection0, Intersections),
  (  member(OrderKey, [??, ?<]), Intersection0 = singleton(Y)
  -> arg(1, X, X1), arg(1, Y, Y1), X1 = Y1, dom_normalized(Intersection0, Intersection)
  ;  Intersection = Intersection0
  ).

% terms_intersection([+X, +Y], terms_to(+Z), -Intersection) is multi.
%
% Intersection of an upper-bounded domain with a closed interval. Input domains must be 
% normalized first to yield correct answers: see `dom_normalized/2`.
terms_intersection_int_to([X, Y], terms_to(Z), Intersection) :-
  terms_intersection_to_int(terms_to(Z), [X, Y], Intersection).

% Helper predicate for building keys for lookup 
terms_orderKey(X, Y, Z, W, XrW, YrZ, OrderKey) :-
  term_order(X, Z, XrZ),
  term_order(Y, W, YrW),
  atom_chars(OrderKey, [XrZ, XrW, YrZ, YrW]).

% Lookup table for intersecting two closed intervals 
terms_int_int_lookup(<<><, _, Y, Z, _, [[Z,Y]]).
terms_int_int_lookup(<<>=, _, Y, Z, _, [[Z,Y]]).
terms_int_int_lookup(=<><, _, Y, Z, _, [[Z,Y]]).
terms_int_int_lookup(=<>=, _, Y, Z, _, [[Z,Y]]).
terms_int_int_lookup(<<>>, _, _, Z, W, [[Z,W]]).
terms_int_int_lookup(=<>>, _, _, Z, W, [[Z,W]]).
terms_int_int_lookup(><><, X, Y, _, _, [[X,Y]]).
terms_int_int_lookup(><>=, X, Y, _, _, [[X,Y]]).
terms_int_int_lookup(><>>, X, _, _, W, [[X,W]]).
terms_int_int_lookup(<?>?, _, Y, Z, W, [[Z,W], [Z,Y]]).
terms_int_int_lookup(=?>?, _, Y, Z, W, [[Z,W], [Z,Y]]).
terms_int_int_lookup(=???, _, Y, Z, W, [[Z,W], [Z,Y]]).
terms_int_int_lookup(=<??, _, Y, Z, W, [[Z,W], [Z,Y]]).
terms_int_int_lookup(><??, X, Y, _, W, [[X,W], [X,Y]]).
terms_int_int_lookup(?<?=, X, Y, Z, _, [[Z,Y], [X,Y]]).
terms_int_int_lookup(??><, X, Y, Z, _, [[Z,Y], [X,Y]]).
terms_int_int_lookup(??>=, X, Y, Z, _, [[Z,Y], [X,Y]]).
terms_int_int_lookup(???=, X, Y, Z, _, [[Z,Y], [X,Y]]).
terms_int_int_lookup(?<?>, X, _, Z, W, [[Z,W], [X,W]]).
terms_int_int_lookup(<<??, _, Y, Z, W, [[Z,W], [Z,Y], singleton(Z), empty]).
terms_int_int_lookup(<???, _, Y, Z, W, [[Z,W], [Z,Y], singleton(Z), empty]).
terms_int_int_lookup(>?>?, X, Y, _, W, [[X,W], [X,Y], singleton(X), empty]).
terms_int_int_lookup(>???, X, Y, _, W, [[X,W], [X,Y], singleton(X), empty]).
terms_int_int_lookup(?<?<, X, Y, Z, _, [[Z,Y], [X,Y], singleton(Y), empty]).
terms_int_int_lookup(???<, X, Y, Z, _, [[Z,Y], [X,Y], singleton(Y), empty]).
terms_int_int_lookup(??>>, X, _, Z, W, [[Z,W], [X,W], singleton(W), empty]).
terms_int_int_lookup(???>, X, _, Z, W, [[Z,W], [X,W], singleton(W), empty]).
terms_int_int_lookup(?<??, X, Y, Z, W, [[Z,W], [X,W], [Z,Y], [X,Y], singleton(Y), empty]).
terms_int_int_lookup(??>?, X, Y, Z, W, [[Z,W], [X,W], [Z,Y], [X,Y], singleton(X), empty]).
terms_int_int_lookup(????, X, Y, Z, W, [[Z,W], [X,W], [Z,Y], [X,Y], singleton(X), singleton(Y), empty]).

% terms_intersection([+X, +Y], [+Z, +W], -Intersection) is multi.
%
% Intersection of two closed intervals.  Input domains must be normalized first to yield correct 
% answers: see `dom_normalized/2`.
terms_intersection_int_int([X, Y], [Z, W], Intersection) :-
  (  Y == Z
  -> Intersection = singleton(Y)
  ;  X == W
  -> Intersection = singleton(X)
  ;  term_order(X, W, XrW),
     term_order(Y, Z, YrZ),
     (  YrZ = '<'
     -> Intersection = empty
     ;  XrW = '>'
     -> Intersection = empty
     ;  YrZ = '='
     -> Intersection = singleton(Y)
     ;  XrW = '='
     -> Intersection = singleton(X)
     ;  terms_orderKey(X, Y, Z, W, XrW, YrZ, OrderKey),
        terms_int_int_lookup(OrderKey, X, Y, Z, W, Intersections),
        member(Intersection0, Intersections),
        (  member(OrderKey, [<<??, <???]), Intersection0 = singleton(Z)
        -> arg(1, Y, Y1), arg(1, Z, Z1), Y1 = Z1, dom_normalized(Intersection0, Intersection)
        ;  member(OrderKey, [>?>?, >???, ??>?]), Intersection0 = singleton(X)
        -> arg(1, X, X1), arg(1, W, W1), X1 = W1, dom_normalized(Intersection0, Intersection)
        ;  member(OrderKey, [?<?<, ?<??, ???<]), Intersection0 = singleton(Y)
        -> arg(1, Y, Y1), arg(1, Z, Z1), Y1 = Z1, dom_normalized(Intersection0, Intersection)
        ;  member(OrderKey, [??>>, ???>]), Intersection0 = singleton(W)
        -> arg(1, X, X1), arg(1, W, W1), X1 = W1, dom_normalized(Intersection0, Intersection)
        ;  OrderKey = ????, dif(X,Y)
        -> (  Intersection0 = singleton(X)
           -> arg(1, X, X1), arg(1, W, W1), X1 = W1, dom_normalized(Intersection0, Intersection)
           ;  Intersection0 = singleton(Y) 
           -> arg(1, Y, Y1), arg(1, Z, Z1), Y1 = Z1, dom_normalized(Intersection0, Intersection)
           ;  Intersection = Intersection0
           ) 
        ;  Intersection = Intersection0
        )
      )
  ).

% Helper predicate 
terms_intersection_from_singleton(terms_from(X), singleton(Y), Intersection) :-
  (  X = const(X1)
  -> (  Y = const(Y1)
     -> (  X1 @=< Y1
        -> Intersection = singleton(Y) 
        ;  Intersection = empty
        )
     ;  Y = variable(Y1)
     -> ( Intersection = empty 
        ; Intersection = singleton(Y), term_indomain(Y1, terms_from(X))
        )
     )
  ; X = variable(X1)
  ->  (  Y = const(_)
      -> ( Intersection = empty
         ; Intersection = singleton(Y), term_indomain(X1, terms_to(Y))
         )
      ;  Y = variable(Y1)
      -> ( Intersection = empty
         ; Intersection = singleton(Y), term_indomain(X1, terms_to(Y)), term_indomain(Y1, terms_from(X))
         )
      )
  ).

% Helper predicate 
terms_intersection_to_singleton(terms_to(X), singleton(Y), Intersection) :-
  (  X = const(X1)
  -> (  Y = const(Y1)
     -> (  X1 @>= Y1 
        -> Intersection = singleton(Y)
        ;  Intersection = empty
        )
     ;  Y = variable(Y1)
     -> ( Intersection = empty
        ; Intersection = singleton(Y), term_indomain(Y1, terms_to(X))
        )
     )
  ;  X = variable(X1)
  -> (  Y = const(_)
     -> ( Intersection = empty
        ; Intersection = singleton(Y), term_indomain(X1, terms_from(Y))
        )
     ;  Y = variable(Y1)
     -> ( Intersection = empty
        ; Intersection = singleton(Y), term_indomain(Y1, terms_to(X)), term_indomain(X1, terms_from(Y))
        )
     )
  ).

% Helper predicate 
terms_intersection_int_singleton([X, Z], singleton(Y), Intersection) :-
  (  X = const(X1)
  -> (  Y = const(Y1)
     -> (  Z = const(Z1)
        -> (  X1 @=< Y1, Y1 @=< Z1
           -> Intersection = singleton(Y)
           ;  Intersection = empty
           )
        ;  Z = variable(Z1)
        -> (  Intersection = empty
           ;  Intersection = singleton(Y), term_indomain(Z1, terms_from(Y))
           )
        )
     ;  Y = variable(Y1)
     -> (  Z = const(_)
        -> (  Intersection = empty
           ;  Intersection = singleton(Y), term_indomain(Y1, [X, Z])
           )
        ;  Z = variable(Z1)
        -> (  Intersection = empty
           ;  Intersection = singleton(Y), term_indomain(Y1, [X, Z]), term_indomain(Z1, terms_from(Y))
           )
        )
     )
  ;  X = variable(X1)
  -> (  Y = const(_)
     -> (  Z = const(_)
        -> ( Intersection = empty
           ; Intersection = singleton(Y), term_indomain(X1, terms_to(Y))
           )
        ;  Z = variable(Z1)
        -> ( Intersection = empty
           ; Intersection = singleton(Y), term_indomain(X1, terms_to(Y)), term_indomain(Z1, terms_from(Y))
           )
        )
     ;  Y = variable(Y1)
     -> (  Z = const(_)
        -> ( Intersection = empty
           ; Intersection = singleton(Y), term_indomain(Y1, [X, Z]), term_indomain(X1, terms_to(Y))
           )
        ;  Z = variable(_)
        -> ( Intersection = empty
           ; Intersection = singleton(Y), term_indomain(Y1, [X, Z])
           )
        )
     )
  ).

% Helper predicate
terms_intersection_singleton_singleton(singleton(X), singleton(Y), Intersection) :-
  (  X = const(X1), Y = const(Y1)
  -> (  X1 = Y1
     -> Intersection = singleton(X)
     ;  Intersection = empty
     )
  ;  X = const(X1), Y = variable(Y1)
  -> ( Intersection = singleton(X), X1 = Y1 ; Intersection = empty )
  ;  X = variable(X1), Y = const(Y1)
  -> ( Intersection = singleton(Y), X1 = Y1 ; Intersection = empty )
  ;  X = variable(X1), Y = variable(Y1)
  -> (  Intersection = singleton(X), X1 = Y1 ; Intersection = empty )
  ).

% terms_dom_intersection(+Dom1, +Dom2, -Intersection) is multi.
%
% Intersection of any two term domains for the standard ordering on terms. Domains are normalized
% first before the intersection is computed. 
terms_dom_intersection(Dom1, Dom2, Intersection) :-
  dom_normalized(Dom1, NewDom1),
  dom_normalized(Dom2, NewDom2),
  (  NewDom1 == all_terms
  -> Intersection = NewDom2
  ;  NewDom2 == all_terms
  -> Intersection = NewDom1
  ;  (NewDom1 == empty ; NewDom2 == empty)
  -> Intersection = empty
  ;  NewDom2 = singleton(_) 
  -> (  NewDom1 = terms_from(_)
     -> terms_intersection_from_singleton(NewDom1, NewDom2, Intersection)
     ;  NewDom1 = terms_to(_)
     -> terms_intersection_to_singleton(NewDom1, NewDom2, Intersection) 
     ;  NewDom1 = [_, _]
     -> terms_intersection_int_singleton(NewDom1, NewDom2, Intersection)
     ;  NewDom1 = singleton(_)
     -> terms_intersection_singleton_singleton(NewDom1, NewDom2, Intersection) 
     )
  ;  NewDom1 = singleton(_), member(NewDom2, [terms_from(_), terms_to(_), [_,_]])
  -> terms_dom_intersection(Dom2, Dom1, Intersection)
  ;  NewDom1 = terms_from(_)
  -> (  NewDom2 = terms_from(_)
     -> terms_intersection_from_from(NewDom1, NewDom2, Intersection)
     ;  NewDom2 = terms_to(_)
     -> terms_intersection_from_to(NewDom1, NewDom2, Intersection)
     ;  NewDom2 = [_,_]
     -> terms_intersection_from_int(NewDom1, NewDom2, Intersection)
     )
  ;  NewDom1 = terms_to(_)
  -> (  NewDom2 = terms_from(_)
     -> terms_intersection_to_from(NewDom1, NewDom2, Intersection)
     ;  NewDom2 = terms_to(_)
     -> terms_intersection_to_to(NewDom1, NewDom2, Intersection)
     ;  NewDom2 = [_,_]
     -> terms_intersection_to_int(NewDom1, NewDom2, Intersection)
     )
  ;  NewDom1 = [_,_]
  -> (  NewDom2 = terms_from(_)
     -> terms_intersection_int_from(NewDom1, NewDom2, Intersection)
     ;  NewDom2 = terms_to(_)
     -> terms_intersection_int_to(NewDom1, NewDom2, Intersection)
     ;  NewDom2 = [_,_]
     -> terms_intersection_int_int(NewDom1, NewDom2, Intersection)
     )
  ).
  
% Hook for term unification in the new "clp_term" domain 
attr_unify_hook(Dom1, Term2) :-
  dom_normalized(Dom1, NewDom1),
  (  get_attr(Term2, clp_term, Dom2)        % Term2 is already attributed
  -> terms_dom_intersection(NewDom1, Dom2, I),
     (  I == empty                     % Fail to unify if resulting domain is empty
     -> fail
     ;  I = singleton(Value)           % New domain is a singleton, so delete attribute and unify normally 
     -> arg(1, Value, Value1),
        del_attr(Term2, clp_term),
        Term2 = Value1
     ;  put_attr(Term2, clp_term, I)   % Otherwise, just set the new domain
     )
  ;  (  nonvar(Term2)
     -> (  NewDom1 == all_terms        % Term2 is not a variable, so check if it belongs to Dom1
        -> true 
        ;  NewDom1 = terms_from(X)     % Lower bound case
        -> (  X = const(X0)
           -> Term2 @>= X0
           ;  X = variable(X0)
           -> term_at_most(X0, Term2) 
           )
        ;  NewDom1 = terms_to(X)       % Upper bound case
        -> (  X = const(X0) 
           -> Term2 @=< X0
           ;  X = variable(X0)
           -> term_at_least(X0, Term2)
           )
        ;  NewDom1 = [X, Y]            % Interval case
        -> (  X = const(X0)
           -> (  Y = const(Y0)
              -> Term2 @>= X0, Term2 @=< Y0
              ;  Y = variable(Y0)
              -> Term2 @>= X0, term_at_least(Y0, Term2)
              )
           ;  X = variable(X0)
           -> (  Y = const(Y0)
              -> term_at_most(X0, Term2), Term2 @=< Y0 
              ;  Y = variable(Y0)
              -> term_at_most(X0, Term2), term_at_least(Y0, Term2)  
              )
           )
        )
     )
  ).

% attribute_termorder_goals(+Term, +Dom, -ResidualGoals) is det.
% List of `ResidualGoals` for `Term` subject to outstanding constraints from `Dom`
attribute_termorder_goals(Term, Dom, ResidualGoals) :-
  (  Dom = terms_from(X), arg(1, X, X0)
  -> ResidualGoals = [term_at_least(Term, X0)]
  ;  Dom = terms_to(Y), arg(1, Y, Y0)
  -> ResidualGoals = [term_at_most(Term, Y0)]
  ;  Dom = [X, Y], arg(1, X, X0), arg(1, Y, Y0)
  -> ResidualGoals = [term_at_least(Term, X0), term_at_most(Term, Y0)]
  ;  Dom = singleton(X), arg(1, X, X0)
  -> ResidualGoals = [is_singleton_term(Term, X0)]
  ;  Dom == empty
  -> ResidualGoals = [is_empty_term(Term)]
  ;  Dom == all_terms
  -> ResidualGoals = [is_term(Term)]
  ).

attribute_goals(Term) -->
  { get_attr(Term, clp_term, Dom0),
    dom_normalized(Dom0, Dom1),
    attribute_termorder_goals(Term, Dom1, ResidualGoals) 
  },
  ResidualGoals.

