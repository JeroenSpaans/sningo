% ------------------------------------------------------------------------------
% METAPROGRAM FOR SUPPORTED MODELS (FIXPOINTS OF IMMEDIATE CONSEQUENCE)
% ------------------------------------------------------------------------------


% ------------------------------------------------------------------------------
% LOGIC HELPERS
% ------------------------------------------------------------------------------
% Lower and upper bound are 'models'
model(l;u).
% We consider positive and negative evaluation for positive atoms and strongly negated atoms respectively
polarity(p;n).
% the initial step under consideration is '0'
step(0).

% Negation mappings from symbols to literals
literal(Name,Number) :- output(Name,LitTup), literal_tuple(LitTup,Number).
literalStrongNegationOf(NegLit,PosLit) :- symbolStrongNegationOf(NegSym,PosSym), literal(NegSym,NegLit), literal(PosSym,PosLit).

% four values determined by IC_P (L,U)
holds(A,l,p,I+1) :- rule(disjunction(H),normal(B)), atom_tuple(H,A), not literalStrongNegationOf(A,_), step(I), bodySatisfied(B,l,u,I).
holds(N,l,n,I+1) :- rule(disjunction(H),normal(B)), atom_tuple(H,A), literalStrongNegationOf(A,N),     step(I), bodySatisfied(B,l,u,I).
holds(A,u,p,I+1) :- rule(disjunction(H),normal(B)), atom_tuple(H,A), not literalStrongNegationOf(A,_), step(I), bodySatisfied(B,u,l,I).
holds(N,u,n,I+1) :- rule(disjunction(H),normal(B)), atom_tuple(H,A), literalStrongNegationOf(A,N),     step(I), bodySatisfied(B,u,l,I).

% hat((L,U))
bodySatisfied(B,M1,M2,I) :- literal_tuple(B), model(M1), model(M2), step(I),
    holds(A,M1,p,I)     : literal_tuple(B,A),   not literalStrongNegationOf(A,_), A > 0;  % not weakly negated, not strongly negated
    holds(N,M1,n,I)     : literal_tuple(B,A),   literalStrongNegationOf(A,N),     A > 0;  % not weakly negated, strongly negated
    not holds(A,M2,p,I) : literal_tuple(B,-A),  not literalStrongNegationOf(A,_), A > 0;  % weakly negated, not strongly negated
    not holds(N,M2,n,I) : literal_tuple(B,-A),  literalStrongNegationOf(A,N),     A > 0.  % weakly negated, strongly negated

% ------------------------------------------------------------------------------
% CANDIDATE GENERATOR
% ------------------------------------------------------------------------------
{holds(A,M,p,0)} :- model(M), rule(disjunction(H),_), atom_tuple(H,A), not literalStrongNegationOf(A,_).
{holds(N,M,n,0)} :- model(M), rule(disjunction(H),_), atom_tuple(H,A), literalStrongNegationOf(A,N).

% ------------------------------------------------------------------------------
% CANDIDATE TESTERS
% ------------------------------------------------------------------------------
:- holds(A,M,P,0), not holds(A,M,P,1).
:- holds(A,M,P,1), not holds(A,M,P,0).

% ------------------------------------------------------------------------------
% DISPLAY HELPERS
% ------------------------------------------------------------------------------
holdsInLowerPositive(N) :- holds(A,l,p,0), literal(N,A).
holdsInLowerNegative(N) :- holds(A,l,n,0), literal(N,A).
holdsInUpperPositive(N) :- holds(A,u,p,0), literal(N,A).
holdsInUpperNegative(N) :- holds(A,u,n,0), literal(N,A).

#show.
#show holdsInLowerPositive/1.
#show holdsInLowerNegative/1.
#show holdsInUpperPositive/1.
#show holdsInUpperNegative/1.
