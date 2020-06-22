// Not testing this file -- times out
// XFAIL: *

// A BDD is an algebraic data type (the underlying unique table is implicit)
// The BDD variable domain is implicit (v in {0 ..})
datatype Bdd = Node(l: Bdd, h: Bdd, v: int) | I | O


function method min(a:int, b: int): int { if a < b then a else b }

// xints can count BDD levels, with I and O nodes receiving the 
datatype xint = Int(n: int) | Infty
function method x(X:Bdd): xint { if X==O || X==I then Infty else Int(X.v) }
predicate method xless(a:xint, b:xint) { if b==Infty && a!=Infty then true else if a==Infty then false else a.n<b.n }
predicate method xleq(a:xint, b:xint) { if b==Infty then true else if a==Infty then false else a.n<=b.n }
function method xmin(a:xint, b:xint): xint { if xleq(a,b) then a else b }

// BDDs are ordered: on all paths the variable strictly increases
predicate increasing(X: Bdd, P: Bdd)
    requires P != O && P != I 
    decreases X
{ (X==O || X==I || (X.v > P.v && increasing(X.l, X) && increasing(X.h, X))) }
predicate ordered1(X: Bdd, r:int) { X == O || X == I || (X.v >= r && increasing(X.l, X) && increasing(X.h, X)) }
predicate ordered(X: Bdd) { ordered1(X,0) }

// BDDs are reduced: no node has two equal children
predicate reduced(X: Bdd) 
    decreases X
{ X == I|| X == O || (X.h != X.l && reduced(X.h) && reduced(X.l)) }
predicate ror(X: Bdd) { ordered(X) && reduced(X) }

// Follow high edges for BDD X     (X.v > v ==> low(X) == X)
function method hgh(X:Bdd, v:int): Bdd
    requires ordered1(X,v)
    ensures  xless( Int(v), x(hgh(X,v)) )
{ if x(X) == Int(v) then X.h else X }

// Follow low edges for BDD X     (X.v > v ==> low(X) == X)
function method low(X:Bdd, v:int): Bdd
    requires ordered1(X,v)
    ensures  xless( Int(v), x(low(X,v)) )
{ if x(X) == Int(v) then X.l else X }

// check if vector l is in X
predicate contains(X: Bdd, l: seq<bool>)
    requires ordered(X)
    decreases X
{
    match X
    case O => false
    case I => true
    case Node(L,H,v) =>
      if v >= |l| then false
      else if l[v] then contains(H, l) else contains(L, l)
}

// check if vector l is in X
predicate contains2(X: Bdd, l: seq<bool>)
    requires ordered(X)
    decreases X
{
    match X
    case O => false
    case I => true
    case Node(L,H,v) =>
        if v >= |l| then true
        else if l[v] then contains2(H, l) else contains2(L, l)
}

predicate isOr(A: Bdd, B: Bdd, R: Bdd)
    requires ror(A) && ror(B) && ror(R) 
{
    xleq( xmin(x(A),x(B)), x(R) ) && // inductive case for ordered(and(A,B))
    forall l : seq<bool> :: contains2(R,l) <==> contains2(A,l) || contains2(B,l)
}

// BDD conjoin operation
method or(A: Bdd, B: Bdd) returns (R: Bdd)
    requires ror(A) && ror(B)
    decreases A, B
    ensures ror(R) && isOr(A,B,R)
    ensures forall s: set<nat> :: defOver(A,s) && defOver(B,s) ==> defOver(R,s)
{
    if A==I || B==I { return I; }
    if A==O || A==B { return B; }
    if B==O         { return A; }
    var v := min(A.v, B.v);
    var L := or(low(A,v), low(B,v));
    var H := or(hgh(A,v), hgh(B,v));
    if H == L { return H; }
    R := Node(L, H, v);
}

// Set predicates
predicate disjunct(s: set<nat>, t: set<nat>) { forall i: nat :: !(i in s && i in t) }
predicate defOver(X: Bdd, s: set<nat>) 
    decreases X
{ X == I || X == O || (X.v in s && defOver(X.h, s) && defOver(X.l, s)) } 
  
// Checks if the relation R contains a U b. a contains the values of s, b contains the values of s'
predicate containsR(R: Bdd, a: seq<bool>, b: seq<bool>, s: set<nat>, s': set<nat>)
requires ordered(R)
requires defOver(R, s+s')
decreases R
{
    match R
    case O => false
    case I => true
    case Node(L,H,v) =>
        if v in s then if v >= |a| then false
                       else if a[v] then containsR(H,a,b,s,s') else containsR(L,a,b,s,s')
        else if v >= |b| then false
             else if b[v] then containsR(H,a,b,s,s') else containsR(L,a,b,s,s')
}

method relprev(T: Bdd, R: Bdd, s: set<nat>, ss: set<nat>) returns (S: Bdd)
    requires ror(T) && ror(R)
    requires disjunct(s,ss)
    requires defOver(T, ss)
    requires defOver(R, s+ss)
    decreases R, T
    ensures ror(S)
    ensures defOver(S, s)
    ensures xleq(xmin(x(T),x(R)), x(S))
    ensures forall a: seq<bool> :: contains(S,a) <==> (exists b: seq<bool> :: contains(T,b) && containsR(R,a,b,s,ss)) // CRASHES VERIFIER
{
    assert T == I;

    if T == O || R == O { return O; }
    if T == I && R == I { return I; }
    if R != I && R.v in s 
    {
        var L := relprev(T, R.l, s, ss);
        var H := relprev(T, R.h, s, ss);
        return if L == H then L else Node(L, H, R.v);
    }
    else {
        var m:= if xless(x(R),x(T)) then R.v else T.v;
        var L := relprev(low(T, m), low(R, m), s, ss);
        var H := relprev(hgh(T, m), hgh(R, m), s, ss);
        S := or(L, H);
    }
}
