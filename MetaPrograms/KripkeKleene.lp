% ------------------------------------------------------------------------------
% METAPROGRAM FOR KRIPKE KLEENE (LEAST FIXPOINT OF IMMEDIATE CONSEQUENCE)
% ------------------------------------------------------------------------------


% ------------------------------------------------------------------------------
% LOGIC HELPERS
% ------------------------------------------------------------------------------
% Lower and upper bound are 'models'
model(l;u).
% We consider positive and negative evaluation for positive atoms and strongly negated atoms respectively
polarity(p;n).

% Negation mappings from symbols to literals
literal(Name,Number) :- output(Name,LitTup), literal_tuple(LitTup,Number).
literalStrongNegationOf(NegLit,PosLit) :- symbolStrongNegationOf(NegSym,PosSym), literal(NegSym,NegLit), literal(PosSym,PosLit).

% Immediate Consequence:
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
% CANDIDATE GENERATION AND TESTING
% ------------------------------------------------------------------------------
% At step 0, we start with the least precise approximation
step(0).
holds(A,u,p,0) :- literal_tuple(_,A), not literalStrongNegationOf(A,_), A>0.
holds(A,u,n,0) :- literal_tuple(_,N), literalStrongNegationOf(N,A), N>0.

% The amount of atoms in the program forms an upper bound on the needed steps
% NOTE: I think this upper bound can be shrunk, but we'd have to think about how strong negation affects this.
numberOfAtoms(N) :- #count{L: literal_tuple(_, L)}=N.
potentialStep(0..N) :- numberOfAtoms(N).

% We check for the absence of a fixpoint
% Monotonicity allows us to optimize a little here, only checking change in one direction
noFixpoint(I) :- step(I), not holds(A,l,p,I), holds(A,l,p,I+1).
noFixpoint(I) :- step(I), not holds(A,l,n,I), holds(A,l,n,I+1).
noFixpoint(I) :- step(I), holds(A,u,p,I), not holds(A,u,p,I+1).
noFixpoint(I) :- step(I), holds(A,u,n,I), not holds(A,u,n,I+1).
% Fixpoints are steps which are not no fixpoint
fixpoint(I) :- step(I), not noFixpoint(I).

% We consider steps until the first fixpoint
% By Cousot and Cousot, we know that this fixpoint exists, will be reached, and is the lfp
step(I+1) :- step(I), potentialStep(I+1), noFixpoint(I).
% ------------------------------------------------------------------------------
% DISPLAY HELPERS
% ------------------------------------------------------------------------------
holdsInLowerPositive(N) :- holds(A,l,p,I), literal(N,A), fixpoint(I).
holdsInLowerNegative(N) :- holds(A,l,n,I), literal(N,A), fixpoint(I).
holdsInUpperPositive(N) :- holds(A,u,p,I), literal(N,A), fixpoint(I).
holdsInUpperNegative(N) :- holds(A,u,n,I), literal(N,A), fixpoint(I).

holdsInLowerPositive(N,I) :- holds(A,l,p,I), literal(N,A), fixpoint(I).
holdsInLowerNegative(N,I) :- holds(A,l,n,I), literal(N,A), fixpoint(I).
holdsInUpperPositive(N,I) :- holds(A,u,p,I), literal(N,A), fixpoint(I).
holdsInUpperNegative(N,I) :- holds(A,u,n,I), literal(N,A), fixpoint(I).

#show.
#show holdsInLowerPositive/2.
#show holdsInLowerNegative/2.
#show holdsInUpperPositive/2.
#show holdsInUpperNegative/2.
#show fixpoint/1.
