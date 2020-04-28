/*

Package for G-modules in magma to make use of the decomposition

Authors: Justin McInroy, Sergey Shpectorov
With thanks to Dmitrii Pasechnik
*/

/*
=======  Background  =======

Suppose W is a semisimple G-module (always true in char 0, or where the characteristic doesn't divide |G|)

W \cong U_1^1 \oplus ... \oplus U_1^{k_1} \oplus ... \oplus U_n^1 \oplus ... \oplus U_n^{k_n}

where the set of different irreducible constituents of W are U_1, ..., U_n and these have multiplicity k_1, ..., k_n.

Note that

U_i^1 \oplus ... \oplus U_i^{k_i} \cong \mathbb{F}^{k_i} \otimes U_i

We wish to represent W as

M = \bigoplus_{i=1}^n \mathbb{F}^{k_i} \otimes U_i

In particular, elements of \mathbb{F}^{k_i} \otimes U_i are just k_i x Dimension(U_i) matrices and finding the submodule spanned by such elements is just taking the column span

*/
declare type GModDec[GModDecElt];

declare attributes GModDec:
  group,              // The group G
  ring,               // The base ring of M
  irreducibles,       // A SeqEnum of all the irreducibles for the group G
  multiplicities,     // A SeqEnum of the multiplicities of each irreducible
  subspaces,          // A SeqEnum of subspaces of the corresponding multiplicity
  tensors,            // A List of Lists of tuples <S, iso>, where S lists the multiplicities of the irreducibles in the tensor product and iso is an isomorphism from the tensor product in the normal sense, to our decomposed version.  Initialised to false instead of the tuple.
  symmetric_squares,  // A List <S, iso>, where S lists the multiplicities of the irreducibles in the symmetric square and iso is an isomorphism from the symmetric square in the normal sense, to our decomposed version.  Initialised to false instead of the tuple.
  restrictions;       // An Assoc with keys being the subgroup H we restrict to and the entry being a List of tuples < N, A, [ phi_1, ..., phi_k]>, indexed by irreducibles U_i of the GModDec for G, where N =  \bigoplus_{i=1}^n \mathbb{F}^{k_i} \otimes V_i is a GModDec for H, A is a change of basis matrix from U_i to N (considered as a direct sum of modules), and phi_j is a projection map from \mathbb{F}^{k_j} to a 1-dimensional vector space S (where U_i = S \otimes U_i)
 
declare attributes GModDecElt:
  parent,           // Parent
  elt;              // A List of matrices, one for each irreducible.

declare verbose GModDec, 4;
/*

=======  Functions for a GModDec  =======

*/
intrinsic Print(M::GModDec)
  {
  Prints a GModDec.
  }
  printf "DecomposedGModule of dimension %o over %o", Dimension(M), BaseRing(M);
end intrinsic;

intrinsic Group(M::GModDec) -> Grp
  {
  The group G of the G-module M.
  }
  return M`group;
end intrinsic;

intrinsic BaseRing(M::GModDec) -> Rng
  {
  Base ring of the module.
  }
  return M`ring;
end intrinsic;

intrinsic Irreducibles(M::GModDec) -> SeqEnum
  {
  Returns the irreducibles for G, where M is a G-module.
  }
  return M`irreducibles;
end intrinsic;

intrinsic Multiplicities(M::GModDec) -> SeqEnum
  {
  Returns the multiplicities of each irreducible for G in M.
  }
  return M`multiplicities;
end intrinsic;

intrinsic Multiplicity(M::GModDec, i::RngIntElt) -> RngIntElt
  {
  The multiplicity of the ith irreducible in M.
  }
  return M`multiplicities[i];
end intrinsic;

intrinsic Multiplicity(M::GModDec, U::ModGrp) -> RngIntElt
  {
  The multiplicity of U in M.
  }
  irreds := Irreducibles(M);
  assert exists(i){i : i in [1..#irreds] | IsIsomorphic(U, irreds[i])};
  return Multiplicity(M, i);
end intrinsic;

intrinsic Subspaces(M::GModDec) -> SeqEnum
  {
  Returns the sequences of the subspaces for the decompositon of M.
  }
  return M`subspaces;
end intrinsic;

intrinsic Subspace(M::GModDec, i::RngIntElt) -> SeqEnum
  {
  Returns subspaces for the ith homogeneous component in the decompositon of M.
  }
  return M`subspaces[i];
end intrinsic;

intrinsic Dimension(M::GModDec) -> RngIntElt
  {
  Dimension of the module.
  }
  mults := Multiplicities(M);
  irreds := Irreducibles(M);
  return forall{m : m in mults | m eq 0} select 0 else 
         &+[ mults[i]*Dimension(irreds[i]) : i in [1..#irreds] | mults[i] ne 0];
end intrinsic;

intrinsic OverDimension(M::GModDec) -> RngIntElt
  {
  Dimension of the full module containing M.
  }
  dims := [OverDimension(V) : V in Subspaces(M)];
  irreds := Irreducibles(M);
  return forall{m : m in dims | m eq 0} select 0 else 
         &+[ dims[i]*Dimension(irreds[i]) : i in [1..#irreds] | dims[i] ne 0];
end intrinsic;

intrinsic GModuleAction(M::GModDec) -> Map
  {
  Returns the action homomorphism of M
  }
  irreds := Irreducibles(M);
  return hom< Group(M) -> GL(Dimension(M), BaseRing(M)) | g:-> DiagonalJoin(< g@GModuleAction(irreds[i]) : j in [1..Multiplicities(M, i)], i in [1..#irreds]>)>;  
end intrinsic;

intrinsic Hash(M::GModDec) -> RngIntElt
  {
  The hash of the module.
  }
  return Hash(<Group(M), BaseRing(M), Subspaces(M)>);
end intrinsic;
/*

=======  Creating a GModDec  =======

*/
intrinsic DecomposedGModule(M::GModDec) -> GModDec, AlgMatElt
  {
  The GModDec of the magma G-module M.
  }
  return M, IdentityMatrix(BaseRing(M), Dimension(M));
end intrinsic;
/*

We will need to know the decomposition of a magma GModule into irreducibles and a change of basis matrix into those

*/
function GetDecomposition(W: irreds := IrreducibleModules(Group(W), BaseRing(W)))
  G := Group(W);
  F := BaseRing(W);
  
  if F eq Rationals() then
    T := RationalCharacterTable(G);
    char := Character(W);
    mults := ChangeUniverse(Decomposition(T, char), Integers());
    dec := Decomposition(W);
    // NB the decomposition may not be in order of T
    Sort(~dec, func<A,B | Position(T,Character(A)) - Position(T, Character(B))>);
  else
    dec := Decomposition(W);
    iso_class := {* i where so := exists(i){i : i in [1..#irreds] | IsIsomorphic(U, irreds[i])} : U in dec *};
    mults := ChangeUniverse([ Multiplicity(iso_class, i) : i in [1..#irreds]], Integers());
    // NB the decomposition may not be in order of T
    T := CharacterTable(G);
    Sort(~dec, func<A,B | Position(T,Character(A)) - Position(T, Character(B))>);
  end if;
  
  abs_irred := [ Dimension(EndomorphismAlgebra(irreds[i])) eq 1 : i in [1..#irreds] | mults[i] ne 0];
  
  if false in abs_irred then
    print "WARNING - one of the irreducibles is not absolutely irreducible.  Any calculations may well be incorrect!";
  end if;

  return irreds, mults, dec;
end function;

intrinsic DecomposedGModule(M::ModGrp) -> GModDec, AlgMatElt
  {
  The GModDec N of the magma G-module M and a change of basis matrix from M to N.
  }
  G := Group(M);
  F := BaseRing(M);
  
  N := New(GModDec);
  N`group := G;
  N`ring := F;
  
  irreds, mults, dec := GetDecomposition(M);
  
  N`irreducibles := irreds;
  N`multiplicities := mults;
  N`subspaces := [ VectorSpace(F, d) : d in mults ];

  N`tensors := [* [* false : j in [1..#irreds]*] : i in [1..#irreds]*];
  N`symmetric_squares := [* false : i in [1..#irreds]*];
  N`restrictions := AssociativeArray();
  
  S := Sort(MultisetToSequence({* i^^mults[i] : i in [1..#irreds]*}));
  CoB := Matrix([ VectorSpace(M) | M!u : u in Basis(U), U in dec])^-1 *
           DiagonalJoin(< iso where so, iso := IsIsomorphic(dec[i], irreds[S[i]]) : i in [1..#dec]>);
  
  return N, CoB;
end intrinsic;

intrinsic DecomposedGModule(G::GrpPerm, F::Fld, S::SeqEnum[RngIntElt]) -> GModDec
  {
  Returns the decomposed G-module over F, with the multiplicity of each irreducible given by S.  (Order is determined via IrreducibleModules.)
  }
  irreds := IrreducibleModules(G, F);
  require #S eq #irreds: "The number of multiplicities should be %o", #irreds;
  
  M := New(GModDec);
  M`group := G;
  M`irreducibles := irreds;
  M`multiplicities := S;
  M`subspaces := [ VectorSpace(F, d) : d in S ];

  M`tensors := [* [* false : j in [1..#irreds]*] : i in [1..#irreds]*];
  M`symmetric_squares := [* false : i in [1..#irreds]*];
  M`restrictions := AssociativeArray();
  
  return M;
end intrinsic;

intrinsic DecomposedGModule(S::SeqEnum[Mtrx]) -> GModDec
  {
  Returns the decomposed G-module generated by the matrices in S.
  }
  // NOT YET IMPLMENTED
  // return null;
end intrinsic;
/*

=======  Submodules and quotients  =======

*/
intrinsic SubConstructor(M::GModDec, X::.) -> GModDec, GModDecHom
  {
  The submodule generated by X and the inclusion map.
  }
  // If we are inputed a set or sequence, then remove the tuple
  if #X eq 1 and Type(X[1]) in {SeqEnum, SetEnum, SetIndx} and forall{x : x in X[1] | Type(x) in { GModDec, ModTupFld, GModDecElt, SeqEnum, ModTupFldElt, ModGrpElt}} then
    X := X[1];
  end if;
  irreds := Irreducibles(M);
  mults := Multiplicities(M);
  subs := Subspaces(M);
  
  Mnew := New(GModDec);
  Mnew`group := Group(M);
  Mnew`ring := BaseRing(M);
  Mnew`irreducibles := irreds;
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  Mnew`restrictions := M`restrictions;
  
  abs_irred := [ Dimension(EndomorphismAlgebra(U)) eq 1 : U in irreds];
  
  if false in abs_irred then
    print "WARNING - one of the irreducibles is not absolutely irreducible.  The answer may well be incorrect!";
  end if;

  if #X eq 0 then
     Mnew`subspaces := [ sub< Generic(U)|> : U in subs ];
  elif Type(X) in {SeqEnum, SetEnum, SetIndx} and forall{x : x in X | Type(x) eq SeqEnum and #x eq OverDimension(M) or Type(x) in {ModTupFldElt, ModGrpElt} and Degree(x) eq OverDimension(M)} then
    
    if Type(X) in {SetEnum, SetIndx} then
      X := Setseq(X);
    end if;
    bigmat := Matrix(X);
    
    dims := [ Dimension(U) : U in irreds];
    offset := [ i eq 1 select 0 else Self(i-1)+dims[i-1]*mults[i-1] : i in [1..#irreds]];
    
    mats := [* VerticalJoin(<Submatrix(bigmat, [1..#X], [ offset[i] + (k-1)*dims[i] + j : k in [1..mults[i]]] ) : j in [1..dims[i]]>)
     : i in [1..#irreds] *];
    
    Mnew`subspaces := [ sub< Generic(subs[i]) | Rows(mats[i])> : i in [1..#irreds]];
  elif Type(X) in {SeqEnum, SetEnum, SetIndx} and forall{x : x in X | Type(x) eq GModDec} then
    return &+X;
  elif Type(X) in {SeqEnum, SetEnum, SetIndx} and forall{x : x in X | Type(x) eq ModTupFld} and #X eq #irreds and forall{ i : i in [1..#X] | OverDimension(X[i]) eq OverDimension(subs[i]) and X[i] subset subs[i]} then
    Mnew`subspaces := X;
  elif (Type(X) in {SeqEnum, SetEnum, SetIndx} and forall{x : x in X | Type(x) eq GModDecElt})
        or (#X eq 1 and IsCoercible(M, X[1])) then
    // We have a set/sequence of GModDecElts or a tuple of a single element
    XX := { M | x : x in X };

    // We want to take the column span of each element
    Mnew`subspaces := [ sub< Generic(subs[i]) | Flat([ Rows(Transpose(x`elt[i])) : x in XX])> : i in [1..#irreds]];
  else
    require false: "RHS is not understood.";
  end if;
  
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];

  // Have to do Morphisms rather than use the inclusion map coming from the sub constructor otherwise Image is not computable sometimes!
  /*
  incs := [ hom<Mnew`subspaces[i]-> subs[i] | Rows(Morphism(Mnew`subspaces[i], subs[i]))>
             : i in [1..#irreds]];
  */
  // The second component returns a map, not a GModDecHom.  It can be applied to elements and knows the domain and codomain, but not the image and you can't access the GModDecHom structure.  Don't know how to make this work!
  return Mnew; //, Hom(Mnew, M, incs);
end intrinsic;

intrinsic Morphism(N::GModDec, M::GModDec) -> GModDecHom
  {
  If N was created as a submodule of M, return the inclusion homomorphism.
  }
  require N subset M: "The second module is a not a subset of the first.";
  Msubs := Subspaces(M);
  Nsubs := Subspaces(N);
  
  incs := [ hom<Nsubs[i]-> Msubs[i] | Rows(Morphism(Nsubs[i], Msubs[i]))> : i in [1..#Msubs]];
  return Hom(N, M, incs);
end intrinsic;

intrinsic QuoConstructor(M::GModDec, X::.) -> GModDec, GModDecHom
  {
  The quotient of M by the submodule generated by X and the quotient map.
  }
  if #X eq 1 and Type(X[1]) eq SeqEnum and forall{x : x in X[1] | Type(x) in { GModDecElt, SeqEnum, ModTupFldElt, ModGrpElt}} then
    X := X[1];
  elif #X eq 1 and Type(X[1]) eq GModDec and X[1] subset M then
    X := Basis(X[1]);
  end if;
  XX := { M | x : x in X };
  
  Mnew := New(GModDec);
  Mnew`group := Group(M);
  Mnew`ring := BaseRing(M);
  Mnew`irreducibles := Irreducibles(M);
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  Mnew`restrictions := M`restrictions;
  
  quos := [ < Q, psi> where Q, psi := quo< Subspace(M, i) | Flat([ Rows(Transpose(x`elt[i])) : x in XX])> : i in [1..#Multiplicities(M)]];
  
  Mnew`subspaces := [ t[1] : t in quos];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  // the quoconstructor returns a map rather than a GModDecHom element
  return Mnew; //, Hom(M, Mnew, [ t[2] : t in quos]);
end intrinsic;

intrinsic '/'(M::GModDec, N::GModDec) -> GModDec, GModDecHom
  {
  The quotient of M by N and the quotient map.
  }
  return quo<M|N>;
end intrinsic;

// Can't get the QuoConstructor to return a GModDecHom element, so do everything again, just to return this:
intrinsic QuoMap(M::GModDec, X::.) -> GModDecHom
  {
  The quotient of M by the submodule generated by X and also a sequence of quotient maps.
  }
  if Type(X) eq GModDec and X subset M then
    X := Basis(X);
  end if;
  XX := { M | x : x in X };
  
  Mnew := New(GModDec);
  Mnew`group := Group(M);
  Mnew`ring := BaseRing(M);
  Mnew`irreducibles := Irreducibles(M);
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  Mnew`restrictions := M`restrictions;
  
  quos := [ < Q, psi> where Q, psi := quo< Subspace(M, i) | Flat([ Rows(Transpose(x`elt[i])) : x in XX])> : i in [1..#Multiplicities(M)]];
  
  Mnew`subspaces := [ t[1] : t in quos];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  return Hom(M, Mnew, [ t[2] : t in quos]);
end intrinsic;
/*

=======  Direct Sums  =======

*/
// Given cached information about our GModDecs, we want to maintain it when we build new ones.
/*

Given a List Q of Lists, produce the merged version.
Will be used for tensor and symmetric_square attributes

NB elements in the List may be undefined (given by false), but where they are defined, they must agree.

*/
function Merge(Q)
  L := [* *];
  for i in [1..Maximum([#S : S in Q])] do
    if exists(S){S : S in Q | Type(S) ne BoolElt} then
      L[i] := S[i];
    else
      L[i] := false;
    end if;
  end for;

  return L;
end function;
/*

Given a List Q of AssociativeArrays, merge them by combining the information.

*/
function MergeAssoc(Q)
  A := AssociativeArray();
  keys := [Keys(S) : S in Q];
  allkeys := &join keys;
  
  for k in allkeys do
    indexes := [ i : i in [1..#Q] | k in keys[i] ];
    A[k] := Merge(Q[indexes]);
  end for;

  return A;
end function;

intrinsic DirectSum(M::GModDec, N::GModDec) -> GModDec, GModDecHom, GModDecHom, GModDecHom, GModDecHom
  {
  The direct sum of M and N, the two inclusion maps and the two projection maps.
  }
  F := BaseRing(M);
  require Group(M) eq Group(N) and F eq BaseRing(N): "The two modules must be for the same group and over the same field.";
  irreds := Irreducibles(M);
  
  Mnew := New(GModDec);
  Mnew`group := Group(M);
  Mnew`ring := F;
  Mnew`irreducibles := irreds;
  
  Mnew`tensors := [* Merge([* M`tensors[i], N`tensors[i]*]) : i in [1..#irreds]*];
  Mnew`symmetric_squares := Merge([* M`symmetric_squares, N`symmetric_squares *]);
  Mnew`restrictions := MergeAssoc([* M`restrictions, N`restrictions *]);
  
  sums := [ < V, inj1, inj2, proj1, proj2 > 
      where V, inj1, inj2, proj1, proj2 := DirectSum(Subspaces(M, i), Subspaces(N, i))
                   : i in [1..#irreds]];
  
  // The DirectSum(U, V) above returns answer that is a subspace of the direct sum of ambient spaces of U and V.  We don't want this so we need to build some maps and redefine the subspaces.
  
  Mnew`subspaces := [ VectorSpace(F, Dimension(t[1])) : t in sums ];
  homs := [ hom< sums[i,1] -> Mnew`subspaces[i] | Rows(BasisMatrix(Mnew`subspaces[i]))>
              : i in [1..#Mnew`subspaces]];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  inj1 := Hom(M, Mnew, [sums[i,2]*homs[i] : i in [1..#sums]]);
  inj2 := Hom(N, Mnew, [sums[i,3]*homs[i] : i in [1..#sums]]);
  proj1 := Hom(Mnew, M, [homs[i]^-1*sums[i,4] : i in [1..#sums]]);
  proj2 := Hom(Mnew, N, [homs[i]^-1*sums[i,5] : i in [1..#sums]]);
  
  return Mnew, inj1, inj2, proj1, proj2;
end intrinsic;

intrinsic DirectSum(Q::SeqEnum[GModDec]) -> GModDec, SeqEnum, SeqEnum
  {
  The direct sum of the modules in Q, a sequence of inclusion maps and a sequence of projection maps given as matrices.
  }
  require #Q ne 0: "The sequence of Gmodules for the direct sum is empty.";
  F := BaseRing(Q[1]);
  irreds := Irreducibles(Q[1]);
  
  require forall{ M : M in Q | Group(M) eq Group(Q[1])} and forall{ M : M in Q | BaseRing(M) eq F}: "The modules must be for the same group and over the same field.";
  Mnew := New(GModDec);
  Mnew`group := Group(Q[1]);
  Mnew`ring := F;
  Mnew`irreducibles := irreds;
  
  Mnew`tensors := [* Merge([*M`tensors[i] : M in Q*]) : i in [1..#irreds]*];
  Mnew`symmetric_squares := Merge([* M`symmetric_squares : M in Q*]);
  Mnew`restrictions := MergeAssoc([* M`restrictions : M in Q*]);
  
  sums := [ < V, injs, projs > 
      where V, injs, projs := DirectSum([ Subspace(M, i) : M in Q])
                   : i in [1..#irreds]];
  
  // The DirectSum above returns answer that is a subspace of the direct sum of ambient spaces.  We don't want this so we need to build some maps and redefine the subspaces.
  
  Mnew`subspaces := [ VectorSpace(F, Dimension(t[1])) : t in sums ];
  homs := [ hom< sums[i,1] -> Mnew`subspaces[i] | Rows(BasisMatrix(Mnew`subspaces[i]))>
              : i in [1..#Mnew`subspaces]];
  homsinv := [ f^-1 : f in homs];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  injs := [ Hom(Q[j], Mnew, [sums[i,2,j]*homs[i] : i in [1..#sums]]) : j in [1..#Q]];
  projs := [ Hom(Mnew, Q[j], [homsinv[i]*sums[i,3,j] : i in [1..#sums]]) : j in [1..#Q]];
  
  return Mnew, injs, projs;
end intrinsic;
/*

=======  Tensors and symmetric squares  =======

*/

/*

Given a GModDec M, return the tensor product of the ith and jth irreducibles, calculating and caching it if necessary.

Same for symmetric square

*/
function GetTensor(M, i, j)
  t := Cputime();
  irreds := Irreducibles(M);
  
  if j lt i then
    // only calculate the isomorphism one way round
    S, iso := GetTensor(M, j, i);
    seq := [ [k,l] : k in [1..Dimension(irreds[i])], l in [1..Dimension(irreds[j])]];
    Sort(~seq, ~perm);
    P := PermutationMatrix(BaseRing(M), perm);
    
    isorev := P*iso;
    return S, isorev;
  end if;
  
  if Type(M`tensors[i,j]) eq BoolElt then
    vprint GModDec, 2: "Calculating tensor.";

    UxV := TensorProduct(irreds[i], irreds[j]);
    
    if BaseRing(M) eq Rationals() then
      T := RationalCharacterTable(Group(M));
      char := Character(UxV);
      S := ChangeUniverse(Decomposition(T, char), Integers());
      SS := Sort(MultisetToSequence({* i^^S[i] : i in [1..#irreds]*}));
    else
      dec := Decomposition(UxV);
      SS := Sort(MultisetToSequence({* i where so := exists(i){i : i in [1..#irreds] | IsIsomorphic(U, irreds[i])} : U in dec *}));
      S := [ Multiplicity(SS, i) : i in [1..#irreds]];
      // This assumes that the field is the splitting field for the characters of G
      T := CharacterTable(Group(M));
    end if;
    
    N := DirectSum([ irreds[i] : i in SS]);
    
    /*
    tt := Cputime();
    so, iso := IsIsomorphic(UxV, N);
    vprintf GModDec, 4: "Time taken for isomorphic method: %o.\n", Cputime(tt);
    */
    
    // I think using characters will be quicker
    tt := Cputime();
    inds := IndecomposableSummands(UxV);
    charpos := [Position(T, Character(U)) : U in inds];
    Sort(~charpos, ~perm);
    inds := PermuteSequence(inds, perm);
    iso := VerticalJoin(< hom*Matrix([UxV!u : u in Basis(inds[i])]) where _, hom := IsIsomorphic(irreds[charpos[i]], inds[i]) : i in [1..#charpos]>)^-1;
    vprintf GModDec, 4: "Time taken for indecomposables method: %o.\n", Cputime(tt);
    
    M`tensors[i,j] := <S, iso>;
  else
     vprint GModDec, 2: "Tensor already cached.";
  end if;
  vprintf GModDec, 4: "Time taken: %o.\n", Cputime(t);
  
  return M`tensors[i,j,1], M`tensors[i,j,2];
end function;

function GetS2(M, i)
  t := Cputime();
  irreds := Irreducibles(M);
  
  if Type(M`symmetric_squares[i]) eq BoolElt then
    vprint GModDec, 2: "Calculating symmetric square.";
    S2 := SymmetricSquare(irreds[i]);
  
    if BaseRing(M) eq Rationals() then
      T := RationalCharacterTable(Group(M));
      char := Character(S2);
      S := ChangeUniverse(Decomposition(T, char), Integers());
      SS := Sort(MultisetToSequence({* i^^S[i] : i in [1..#irreds]*}));
    else
      dec := Decomposition(S2);
      SS := Sort(MultisetToSequence({* i where so := exists(i){i : i in [1..#irreds] | IsIsomorphic(U, irreds[i])} : U in dec *}));
      S := [ Multiplicity(SS,i) : i in [1..#irreds]];
    end if;
    
    N := DirectSum([ irreds[i] : i in SS]);
    so, iso := IsIsomorphic(S2, N);
    
    assert so;
    M`symmetric_squares[i] := <S, iso>;
  else
     vprint GModDec, 2: "Symmetric square already cached.";
  end if;
  vprintf GModDec, 4: "Time taken: %o.\n", Cputime(t);
  
  return M`symmetric_squares[i,1], M`symmetric_squares[i,2];
end function;
/*

Tensor products

*/
intrinsic TensorProduct(M::GModDec, N::GModDec) -> GModDec, GModDecBil
  {
  The tensor product of M and N.
  }
  require Group(M) eq Group(N) and BaseRing(M) eq BaseRing(N): "The two modules must be for the same group and over the same field.";
  
  vprint GModDec, 2: "Calculating the GModDec tensor product.";
  t := Cputime();
  
  if Dimension(M) eq 0 or Dimension(N) eq 0 then
    return sub<M|>, _;
  end if;
  
  F := BaseRing(M);
  no_const := #Irreducibles(M);

  // For each homogeneous component, S_i \otimes U_i and T_j \otimes U_j, their tensor product is \bigotimes_k (S_i \otimes T_j \otimes R_k) \otimes R_k.  We want to know the start position of each S_i \otimes T_j \otimes R_k in the final sum.

  start_pos := [[] : i in [1..no_const]];
  last := [0 : k in [1..no_const]];

  for i in [1..no_const], j in [1..no_const] do
    if Multiplicity(M, i) ne 0 and Multiplicity(N, j) ne 0 then
      R := GetTensor(M, i, j);
      start_pos[i,j] := last;
      last := [ last[k]+Multiplicity(M, i)*Multiplicity(M, j)*R[k] : k in [1..no_const]];
    end if;
  end for;

  Mnew := New(GModDec);
  Mnew`group := Group(M);
  Mnew`ring := F;
  Mnew`irreducibles := Irreducibles(M);
  
  Mnew`tensors := [* Merge([*M`tensors[i], N`tensors[i]*]) : i in [1..no_const]*];
  Mnew`symmetric_squares := Merge([* M`symmetric_squares, N`symmetric_squares*]);
  Mnew`restrictions := MergeAssoc([* M`restrictions, N`restrictions*]);
  
  Mnew`multiplicities := last;
  Mnew`subspaces := [ VectorSpace(F, d) : d in Mnew`multiplicities ];
  vprintf GModDec, 4: "Time taken to build the GModDec tensor product: %o.\n", Cputime(t);
  
  vprint GModDec, 2: "Calculating the isomorphism.";
  tt := Cputime();
  Cat := TensorCategory([1,1,1,-1], {{3},{2},{1},{0}});
  
  bilmaps := [*[**] : i in [1..no_const] *];
  start := [0 : k in [1..no_const]];
  for i in [1..no_const], j in [1..no_const] do
    if Multiplicity(M, i) eq 0 or Multiplicity(M, j) eq 0 then
      assert not IsDefined(start_pos[i], j);
    else
      start := start_pos[i,j];
    end if;
    mult_R := GetTensor(M, i, j);
    R := [ VectorSpace(F, d) : d in mult_R];
    
    injs := [* hom< Im-> Mnew`subspaces[k] |
                              [<Im.l, Mnew`subspaces[k].(l+start[k])> : l in [1..Dimension(Im)]]>
                      where Im := VectorSpace(F, Multiplicity(M, i)*Multiplicity(M, j)*mult_R[k])
                      : k in [1..no_const]*];
    
    bilmaps[i,j] := [* Tensor([*R[k], Subspace(M, i), Subspace(N, j), Mnew`subspaces[k]*],
                   func<x | TensorProduct(TensorProduct(x[1],x[2]),x[3])@injs[k]>, Cat)
                      : k in [1..no_const]*];
  end for;
  
  ten_map := New(GModDecBil);
  ten_map`domain := [* M, N *];
  ten_map`codomain := Mnew;
  ten_map`maps := bilmaps;

  vprintf GModDec, 4: "Time taken to find the isomorphism: %o.\n", Cputime(tt);
  
  vprintf GModDec, 4: "Total time: %o.\n", Cputime(t);
  return Mnew, ten_map;
end intrinsic;
/*

Given two irreducibles U, V, we have already calculated their tensor UxV and an isomorphism iso onto our copy of this which is isomorphic to a direct sum of the contituents of UxV in order.

Suppose that we are doing the tensor of M and N where U \subset M and V subset N.  Then, MxN has the constituents of UxV in some order.

This function gives the image of UxV in our copy of MxN, where S is the list of mulitplicities of irreducibles in UxV and pos is a sequence of sequences [ T_1,..., T_n] where T_k describes the positions in MxN of the kth irreducible in UxV and mult is the multiplicites of the irreducibles in MxN and dims the dimensions of the irreducibles.

*/
function TensorConvert(iso, S, pos, dims, mult)
  // We find how to chop up the images in iso to map onto the homogeneous components.
  dim := NumberOfRows(iso);
  hompos := [ S[i]*dims[i] : i in [1..#S] | S[i] ne 0];
  breakpoints := [ i eq 1 select 0 else Self(i-1)+ hompos[i-1]: i in [1..#hompos+1]];
  
  isoparts := [* ColumnSubmatrixRange(iso, breakpoints[i]+1, breakpoints[i+1]) : i in [1..#breakpoints-1]*];
  
  // Using pos, we find the size of the zero blocks which we need to insert.
  zerodims := [];
  num := 0;
  for i in [1..#S] do
    if pos[i] eq [] then
      // There are no ith irreducibles in the tensor
      num +:= mult[i]*dims[i];
    else
      num +:= (pos[i,1]-1)*dims[i];
      Append(~zerodims, num);
      num := (mult[i]-pos[i,#pos[i]])*dims[i];
    end if;
  end for;
  // Now we must append the last one as well
  Append(~zerodims, num);
  
  assert &+zerodims + dim eq &+[mult[i]*dims[i] : i in [1..#mult]];
  assert #zerodims eq #isoparts+1;
  
  F := BaseRing(iso);
  return HorizontalJoin(< IsOdd(i) select ZeroMatrix(F, dim, zerodims[(i+1) div 2]) else isoparts[i div 2] : i in [1..2*#isoparts+1]>);
end function;

intrinsic TensorProductOld(M::GModDec, N::GModDec) -> GModDec, SeqEnum
  {
  The tensor product of M and N and a sequence of sequences giving the maps on elements of M and N into the tensor.
  }
  require Group(M) eq Group(N) and BaseRing(M) eq BaseRing(N): "The two modules must be for the same group and over the same field.";
  vprint GModDec, 2: "Calculating the GModDec tensor product.";
  
  t := Cputime();
  if Dimension(M) eq 0 or Dimension(N) eq 0 then
    return sub<M|>, _;
  end if;
  
  no_const := #Irreducibles(M);
  
  // We form a sequence of the indices of the irreducibles, taking acount of their multiplicities.
  irreds_M := Sort(MultisetToSequence({* i^^Multiplicity(M, i) : i in [1..no_const]*}));
  irreds_N := Sort(MultisetToSequence({* i^^Multiplicity(N, i) : i in [1..no_const]*}));
  
  // NB #multiset is #set, so we are running over all irreducibles
  // Can do this better taking into account multiplicities, surely??
  poss := [[] : i in [1..#irreds_M]];
  last := [0 : i in [1..no_const]];
  for i in [1..#irreds_M] do
    ii := irreds_M[i];
    for j in [1..#irreds_N] do
      jj := irreds_N[j];
      S := GetTensor(M, ii, jj);
      next := [ last[k]+S[k] : k in [1..no_const]];
      poss[i,j] := [ [last[k]+1..next[k]] : k in [1..no_const]];
      last := next;
    end for;
  end for;
  
  Mnew := New(GModDec);
  Mnew`group := Group(M);
  Mnew`ring := BaseRing(M);
  Mnew`irreducibles := Irreducibles(M);
  
  Mnew`tensors := [* Merge([*M`tensors[i], N`tensors[i]*]) : i in [1..no_const]*];
  Mnew`symmetric_squares := Merge([* M`symmetric_squares, N`symmetric_squares*]);
  Mnew`restrictions := MergeAssoc([* M`restrictions, N`restrictions*]);
  
  mult := next;
  Mnew`multiplicities := mult;
  Mnew`subspaces := [ VectorSpace(BaseRing(M), d) : d in Mnew`multiplicities ];
  vprintf GModDec, 4: "Time taken to build the GModDec tensor product: %o.\n", Cputime(t);
  
  // We want to give a `matrix' for the product, so the i,jth entry is the tensor m_i \otimes n_j
  vprint GModDec, 2: "Calculating the isomorphism.";
  tt := Cputime();
  dims := [ Dimension(U) : U in Mnew`irreducibles];
  
  map := [ [] : i in [1..Dimension(M)]];
  
  offset_i := 0;
  for i in [1..#irreds_M] do
    ii := irreds_M[i];
    offset_j := 0;
    for j in [1..#irreds_N] do
      jj := irreds_N[j];
      S, iso := GetTensor(M, ii, jj);
      
      vects := TensorConvert(iso, S, poss[i,j], dims, mult);
      
      for k in [1..dims[ii]] do
        for l in [1..dims[jj]] do
          map[offset_i+k,offset_j+l] := vects[dims[jj]*(k-1) + l];
        end for;
      end for;
      offset_j +:= dims[jj];
    end for;
    offset_i +:= dims[ii];
  end for;
  vprintf GModDec, 4: "Time taken to find the isomorphism: %o.\n", Cputime(tt);
  
  vprintf GModDec, 4: "Total time: %o.\n", Cputime(t);
  return Mnew, map;
end intrinsic;
/*

Gives the index into the symmetric square of a module of dimension n

*/
intrinsic SymmetricSquare(M::GModDec) -> GModDec, GModDecBil
  {
  The symmetric square of M.
  }
  vprint GModDec, 2: "Calculating the GModDec tensor product.";
  t := Cputime();  

  if Dimension(M) eq 0 then
    return M, _;
  end if;
  
  F := BaseRing(M);
  no_const := #Irreducibles(M);
  
  // For each homogeneous component, S_i \otimes U_i and T_j \otimes U_j, their tensor product or symmetric square is \bigotimes_k (S_i \otimes T_j \otimes R_k) \otimes R_k.  We want to know the start position of each S_i \otimes T_j \otimes R_k in the final sum.
  
  start_pos := [[] : i in [1..no_const]];
  last := [0 : k in [1..no_const]];

  for i in [1..no_const], j in [i..no_const] do
    if Multiplicity(M, i) eq 0 or Multiplicity(M, j) eq 0 then
      continue;
    elif i eq j then
      R2 := GetS2(M, i);
      R := GetTensor(M, i, i);
      
      start_pos[i, i] := last;
      last := [ last[k] + Multiplicity(M, i)*R2[k] + 
                (Multiplicity(M, i)*(Multiplicity(M, i)-1) div 2)*R[k] : k in [1..no_const]];
    else
      R := GetTensor(M, i, j);
      start_pos[i,j] := last;
      last := [ last[k] + Multiplicity(M, i)*Multiplicity(M, j)*R[k] : k in [1..no_const]];
    end if;
  end for;
  
  Mnew := New(GModDec);
  Mnew`group := Group(M);
  Mnew`ring := F;
  Mnew`irreducibles := Irreducibles(M);
  
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  Mnew`restrictions := M`restrictions;
  
  Mnew`multiplicities := last;
  Mnew`subspaces := [ VectorSpace(F, d) : d in Mnew`multiplicities ];
  vprintf GModDec, 4: "Time taken to build the GModDec symmetric square: %o.\n", Cputime(t);
  
  vprint GModDec, 2: "Calculating the isomorphism.";
  tt := Cputime();
  Msubs := Subspaces(M);
  Cat := TensorCategory([1,1,1,-1], {{3},{2},{1},{0}});
  
  bilmaps := [*[**] : i in [1..no_const] *];
  start := [0 : k in [1..no_const]];
  for i in [1..no_const], j in [i..no_const] do
    if Multiplicity(M, i) eq 0 or Multiplicity(M, j) eq 0 then
      assert not IsDefined(start_pos[i], j);
    else
      start := start_pos[i,j];
    end if;
    
    if i eq j then // we need to take the symmetric square
      mult_R2 := GetS2(M, i);
      mult_R := GetTensor(M, i, i);
      
      assert forall{ k : k in [1..no_const] | mult_R2[k] le mult_R[k]};
      // We will consider R2[k] to be embedded in R[k]
      R := [ VectorSpace(F, d) : d in mult_R];
      
      // We build a matrix for the the maps
      // for each k, we want a map from the ordered basis of (R \otimes S) \otimes T to Z
      // 
      injs := [* *];
      for k in [1..no_const] do
        Im := VectorSpace(F, Multiplicity(M, i)^2*mult_R[k]);
        pairs := [];
        Mnew_count:= start[k];
        Im_count := 0;
        for a in [1..Dimension(R[k])], b in [1..Multiplicity(M, i)], c in [b..Multiplicity(M, i)] do
          v := TensorProduct(TensorProduct(R[k].a, Msubs[i].b), Msubs[i].c);
          if b eq c then
            // This is a symmetric square
            if a le R2[k] then
              Mnew_count +:= 1;
              Append(~pairs, <v, Mnew`subspaces[k].Mnew_count>);
            else // this does the projection of the remainder of R to zero
              Append(~pairs, <v, Mnew`subspaces[k]!0>);
            end if;
          else // so b < c
            // This is a tensor product
            Mnew_count +:= 1;
            Append(~pairs, <v, Mnew`subspaces[k].Mnew_count>);
            v := TensorProduct(TensorProduct(R[k].a, Msubs[i].c), Msubs[i].b);
            Append(~pairs, <v, Mnew`subspaces[k].Mnew_count>);
          end if;
        end for;
        Append(~injs, hom< Im-> Mnew`subspaces[k] | pairs>);
      end for;
      
      bilmaps[i,i] := [* Tensor([*R[k], Msubs[i], Msubs[i], Mnew`subspaces[k]*],
                     func<x | TensorProduct(TensorProduct(x[1],x[2]),x[3])@injs[k]>, Cat)
                        : k in [1..no_const]*];
      
    else // This is just the tensor case
      mult_R := GetTensor(M, i, j);
      R := [ VectorSpace(F, d) : d in mult_R];
      
      injs := [* hom< Im-> Mnew`subspaces[k] |
                                [<Im.l, Mnew`subspaces[k].(l+start[k])> : l in [1..Dimension(Im)]]>
                        where Im := VectorSpace(F, Multiplicity(M, i)*Multiplicity(M, j)*mult_R[k])
                        : k in [1..no_const]*];
      
      bilmaps[i,j] := [* Tensor([*R[k], Msubs[i], Msubs[j], Mnew`subspaces[k]*],
                     func<x | TensorProduct(TensorProduct(x[1],x[2]),x[3])@injs[k]>, Cat)
                        : k in [1..no_const]*];
      bilmaps[j,i] := [* Tensor([*R[k], Msubs[j], Msubs[i], Mnew`subspaces[k]*],
                     func<x | TensorProduct(TensorProduct(x[1],x[3]),x[2])@injs[k]>, Cat)
                        : k in [1..no_const]*];
    end if;
  end for;
  
  sym_map := New(GModDecBil);
  sym_map`domain := [* M, M *];
  sym_map`codomain := Mnew;
  sym_map`maps := bilmaps;

  vprintf GModDec, 4: "Time taken to find the isomorphism: %o.\n", Cputime(tt);
  
  vprintf GModDec, 4: "Total time: %o.\n", Cputime(t);
  return Mnew, sym_map;
end intrinsic;

ijpos := function(i,j,n)
  if i le j then
    return &+[ n+1 -k : k in [0..i-1]] -n +j-i;
  else
    return &+[ n+1 -k : k in [0..j-1]] -n +i-j;
  end if;
end function;

intrinsic SymmetricSquareOld(M::GModDec) -> GModDec, SeqEnum
  {
  The symmetric square of M.
  }
  if Dimension(M) eq 0 then
    return M, _;
  end if;
  vprint GModDec, 2: "Calculating the GModDec tensor product.";
  t := Cputime();  

  no_const := #Irreducibles(M);
  
  // We form a sequence of the indices of the irreducibles, taking acount of their multiplicities.
  irreds_M := Sort(MultisetToSequence({* i^^Multiplicity(M, i) : i in [1..no_const]*}));
  
  poss := [[] : i in [1..#irreds_M]];
  last := [0 : i in [1..no_const]];
  for i in [1..#irreds_M] do
    ii := irreds_M[i];
    for j in [i..#irreds_M] do
      if i eq j then
        S := GetS2(M, ii);
      else
        jj := irreds_M[j];
        S := GetTensor(M, ii, jj);
      end if;
      next := [ last[k]+S[k] : k in [1..no_const]];
      poss[i,j] := [ [last[k]+1..next[k]] : k in [1..no_const]];
      last := next;
    end for;
  end for;
  
  Mnew := New(GModDec);
  Mnew`group := Group(M);
  Mnew`ring := BaseRing(M);
  Mnew`irreducibles := Irreducibles(M);
  
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  Mnew`restrictions := M`restrictions;
  
  mult := next;
  Mnew`multiplicities := mult;
  Mnew`subspaces := [ VectorSpace(BaseRing(M), d) : d in Mnew`multiplicities ];
  vprintf GModDec, 4: "Time taken to build the GModDec symmetric square: %o.\n", Cputime(t);
  
  // We want to give a `matrix' for the product, so the i,jth entry is the tensor m_i \otimes n_j
  vprint GModDec, 2: "Calculating the isomorphism.";
  tt := Cputime();
  dims := [ Dimension(U) : U in Mnew`irreducibles];
  
  map := [ [] : i in [1..Dimension(M)]];
  
  offset_i := 0;
  for i in [1..#irreds_M] do
    ii := irreds_M[i];
    offset_j := offset_i;
    for j in [i..#irreds_M] do
      if i eq j then
        jj := ii;
        S, iso := GetS2(M, ii);
        
        vects := TensorConvert(iso, S, poss[i,j], dims, mult);
      
        for k in [1..dims[ii]] do
          for l in [k..dims[ii]] do
            map[offset_i+k,offset_j+l] := vects[ijpos(k,l,dims[ii])];
          end for;
        end for;
        
      else
        jj := irreds_M[j];
        S, iso := GetTensor(M, ii, jj);
     
        vects := TensorConvert(iso, S, poss[i,j], dims, mult);
        
        for k in [1..dims[ii]] do
          for l in [1..dims[jj]] do
            map[offset_i+k,offset_j+l] := vects[dims[jj]*(k-1) + l];
          end for;
        end for;
      end if;
      offset_j +:= dims[jj];
    end for;
    offset_i +:= dims[ii];
  end for;
  vprintf GModDec, 4: "Time taken to find the isomorphism: %o.\n", Cputime(tt);
  
  vprintf GModDec, 4: "Total time: %o.\n", Cputime(t);
  return Mnew, Flat([ map[i][i..Dimension(M)] : i in [1..Dimension(M)]]);
end intrinsic;
/*

=======  Restriction and Induction  =======

*/
/*

Have a function to calculate and cache the restriction for an irreducible

*/
RF := recformat< subgroup:GrpPerm, irreducibles:SeqEnum, restrictions:List>;
/*

For the ith irreducible of M, we calculate the restriction to a subgroup M.  We record a tuple <mult, CoB>, where mult is the multiplicities of the H-irreducibles and CoB is a change of basis matrix from the H-irreducible to the ith irreducible of M.

*/
function GetRestriction(M, i, H)
  if H notin Keys(M`restrictions) then
    // We use a record to cache the restrictions
    M`restrictions[H] := rec<RF | subgroup := H, irreducibles := IrreducibleModules(H, BaseRing(M)), 
                             restrictions := [* false : j in [1..#M`irreducibles] *]>;
  end if;
  if Type(M`restrictions[H]`restrictions[i]) eq BoolElt then
    // We haven't yet calculated this
    V := Restriction(Irreducibles(M)[i], H);
    
    Hirreds := Irreducibles(M`restrictions[H]);
    _, mults, dec := GetDecomposition(V: irreds := Hirreds);
    
    S := Sort(MultisetToSequence({* i^^mults[i] : i in [1..#Hirreds]*}));
    // Not entirely sure if moving the inverse into the DiagonalJoin speeds this up or not.
    CoB := DiagonalJoin(< iso where so, iso := IsIsomorphic(dec[i], Hirreds[S[i]]) : i in [1..#dec]>)^-1*Matrix([ VectorSpace(V) | V!u : u in Basis(U), U in dec]);
    
    M`restrictions[H]`restrictions[i] := <mults, CoB>;//, lifts>;
  end if;

  return M`restrictions[H]`restrictions[i,1], M`restrictions[H]`restrictions[i,2];
end function;
/*

We define a lift record

LiftClass`lifts is a List of Lists where the j,ith entry is a map from the jth homogeneous component of the image (represented as a subspace) to the ith homogeneous component of the domain.

NB should this be a new type???

*/
LiftClass := recformat< domain:GModDec, image:GModDec, lifts:List>;
/*

We have already precomputed and cached the Res(U, H) for each irreducible U.

Now if we do the restriction of M of H it is a sum of 


*/
intrinsic Restriction(M::GModDec, H::Grp: change_of_basis := false) -> GModDec, Rec, AlgMatElt
  {
  Returns the restriction of the G-module M to the H-module Res(M, H) where H is a subgroup of G.  Also returns a LiftClass record where the j,ith entry is a map from the jth homogeneous component of Res(M, H) (represented as a subspace) to the ith homogeneous component of M.  The optional parameter change_of_basis controls whether a (H-equivariant) change of basis matrix from Res(M, H) to M is also returned.
  }
  require H subset Group(M): "The given group is not a subgroup of the group for the module.";
  vprint GModDec, 2: "Calculating the GModDec restriction.";
  
  F := BaseRing(M);
  t := Cputime();
  
  // For the ith Homogeneous component, S_i \otimes U_i, it has a decomposition \bigoplus_j T_j \otimes V_j into a direct sum of H-mods.  These become reordered in the end.
  // We calculate this reordering and save it in poss.  The i,jth position of poss a List [* start pos, end pos *] for the start and end positions of the all the T_j in the decomposition of S_i.
  poss := [ ];
  all_irred_mults := [];
  
  for i in [1..#Irreducibles(M)] do
    if  Multiplicity(M, i) eq 0 then
      continue;
    end if;
    
    irred_mults := GetRestriction(M, i, H);
    all_irred_mults[i] := irred_mults;
    
    if not assigned last then
      // This is the first time through so we initialise variables
      H_irreds := Irreducibles(M`restrictions[H]);
      no_H_irreds := #H_irreds;
      last := [ 0 : j in [1..no_H_irreds]];
    end if;
    next := [ last[k]+M`multiplicities[i]*irred_mults[k] : k in [1..no_H_irreds]];
    poss[i] := [ [* last[k], next[k]*] : k in [1..no_H_irreds]];
    last := next;
  end for;
  
  Mnew := New(GModDec);
  Mnew`group := H;
  Mnew`ring := F;
  Mnew`irreducibles := H_irreds;
  Mnew`multiplicities := next;
  Mnew`subspaces := [ VectorSpace(BaseRing(M), d) : d in Mnew`multiplicities ];
  
  Mnew`tensors := [* [* false : j in [1..#H_irreds]*] : i in [1..#H_irreds]*];
  Mnew`symmetric_squares := [* false : j in [1..#H_irreds]*];
  Mnew`restrictions := AssociativeArray();
  vprintf GModDec, 4: "Time taken to build the GModDec restriction: %o.\n", Cputime(t);
  
  // Now we want to create the change of basis matrix and the lifts.
  
  // We first build the lifts for the modules
  // Could make this a sequence at the expense of having to build it all at once and making the code really complicated.
  all_lifts := [**];
  for j in [1..#Mnew`irreducibles] do
    T_j := Mnew`subspaces[j];
    if Dimension(T_j) eq 0 then
      all_lifts[j] := [* hom< T_j -> S_i | > : S_i in Subspaces(M)*];
      continue;
    end if;
    lifts := [**];
    for i in [1..#M`irreducibles] do
      S_i := Subspaces(M, i);
      if Dimension(S_i) eq 0 then
        lifts[i] := hom< T_j -> S_i | ZeroMatrix(F, Dimension(T_j), Dimension(S_i))>;
      else
        lifts[i] := hom< T_j -> S_i | 
          VerticalJoin( < ZeroMatrix(F, poss[i,j,1], Dimension(S_i)),
             TensorProduct(IdentityMatrix(F, Dimension(S_i)),
                           Matrix(F, all_irred_mults[i,j], 1, [1 : k in [1..all_irred_mults[i,j]]])),
             ZeroMatrix(F, Dimension(T_j) - poss[i,j,2], Dimension(S_i))>)>;
      end if;
    end for;
    all_lifts[j] := lifts;
  end for;
  
  lifts := rec<LiftClass | domain := Mnew, image := M, lifts := all_lifts>;
  
  if change_of_basis then
    /*
    The CoB is the inverse of a map from M (viewed as a direct sum) to Res(M, H).
    This is a composition of
      - a diagonal matrix D whose blocks are the CoB from the irreducible U to Res(U,H), taken with multiplicity
      - a permutation matrix P to reorder the irreducibles into the order of Res(M, H)
    
    We calculate the inverse of each of these and multiply.
    */
    // First get all the CoB matrices
    Mmults := Multiplicities(M);
    CoBs := [* Mmults[i] ne 0 select CoB where _, CoB := GetRestriction(M, i, H) else [] : i in [1..#Mmults]*];

    Dinv := DiagonalJoin(< CoBs[i] : j in [1..Mmults[i]], i in [1..Mmults]>);
    
    Hhomblocks := [ i eq 1 select 0 else Self(i-1) + Dimension(Irreducibles(Mnew)[i-1])*Multiplicity(Mnew, i-1) : i in [1..#Irreducibles(Mnew)]];
    
    perm := [];
    for i in [1..Mmults] do
      if Mmults[i] eq 0 then
        continue;
      end if;
      mults := all_irred_mults[i];
      for k in [1..Mmults[i]] do
        for j in [j : j in [1..#mults] | mults[j] ne 0] do
          perm cat:= [ l eq 1 select Hhomblocks[j] + ((k-1)*mults[j] + poss[i,j,1])*Dimension(H_irreds[j])+1 else Self(l-1)+1 : l in [1..mults[j]*Dimension(H_irreds[j])]];
        end for;
      end for;
    end for;
    Pinv := PermutationMatrix(F, perm)^-1;
    
    CoB := Pinv*Dinv;
    return Mnew, lifts, CoB;
  end if;
  
  return Mnew, lifts, _;
end intrinsic;

intrinsic LiftModule(M::GModDec, lifts::Rec) -> GModDec
  {
  Lift the H-module M to a G-module using lifts.
  }
  require M subset lifts`domain: "The module given is not in the domain of the lift.";
  N := lifts`image;
  Msubs := Subspaces(M);
  return sub< N | [ &+[ Msubs[j]@lifts`lifts[j,i] : j in [1..#Msubs]] : i in [1..#Irreducibles(N)]]>;
end intrinsic;

intrinsic ChangeField(M::GModDec, F::Fld) -> GModDec
  {
  Returns the module defined over the field F.
  }
  // NOT YET IMPLMENTED
  // return null;
end intrinsic;

intrinsic ChangeRing(M::GModDec, R::Rng) -> GModDec
  {
  Returns the module defined over the ring R.
  }
  // NOT YET IMPLMENTED
  // return null;
end intrinsic;

intrinsic Moduli(M::GModDec) -> SeqEnum
  {
  The column moduli of the module M over a Euclidean domain.
  }
  // NOT YET IMPLMENTED
  // return null;
end intrinsic;
/*

=======  Functions on (sub)modules of GModDecs  =======

*/
intrinsic Generic(M::GModDec) -> GModDec
  {
  The module which contains M as a submodule.
  }
  Mnew := New(GModDec);
  Mnew`group := Group(M);
  Mnew`ring := BaseRing(M);
  Mnew`irreducibles := Irreducibles(M);
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  Mnew`restrictions := M`restrictions;
  
  Mnew`subspaces := [ Generic(V) : V in Subspaces(M) ];
  Mnew`multiplicities := [ Dimension(V) : V in Subspaces(Mnew)];
  
  return Mnew;
end intrinsic;

intrinsic 'eq'(M::GModDec, N::GModDec) -> BoolElt
  {
  Equality of two submodules M and N.
  }
  require Group(M) eq Group(N) and BaseRing(M) eq BaseRing(N): "There is no covering module.";
  assert #Irreducibles(M) eq #Irreducibles(N);
  
  return Subspaces(M) eq Subspaces(N);
end intrinsic;

intrinsic IsIsomorphic(M::GModDec, N::GModDec) -> BoolElt, Map
  {
  Returns whether M and N are isomorphic and if so also returns the ismomorphism.
  }
  // NOT YET IMPLMENTED
  // return null;
end intrinsic;

intrinsic 'subset'(N::GModDec, M::GModDec) -> BoolElt
  {
  Whether N is a submodule of M.
  }
  require Group(M) eq Group(N) and BaseRing(M) eq BaseRing(N): "There is no covering module.";
  assert #Irreducibles(M) eq #Irreducibles(N);
  
  return forall{ i : i in [1..#Irreducibles(N)] | Subspace(N, i) subset Subspace(M, i)};
end intrinsic;

intrinsic '+'(M::GModDec, N::GModDec) -> GModDec
  {
  The sum of the two submodules M and N.
  }
  require Group(M) eq Group(N) and BaseRing(M) eq BaseRing(N): "There is no covering module.";
  assert #Irreducibles(M) eq #Irreducibles(N);
  
  Mnew := New(GModDec);
  Mnew`group := Group(M);
  Mnew`ring := BaseRing(M);
  Mnew`irreducibles := Irreducibles(M);
  Mnew`tensors := [* Merge([*M`tensors[i], N`tensors[i]*]) : i in [1..#Irreducibles(M)]*];
  Mnew`symmetric_squares := Merge([* M`symmetric_squares, N`symmetric_squares*]);
  Mnew`restrictions := MergeAssoc([* M`restrictions, N`restrictions*]);
  
  Mnew`subspaces := [ M`subspaces[i] + N`subspaces[i] : i in [1..#Irreducibles(M)]];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  return Mnew;
end intrinsic;

intrinsic 'meet'(M::GModDec, N::GModDec) -> GModDec
  {
  The intersection of two submodules M and N.
  }
  require Group(M) eq Group(N) and BaseRing(M) eq BaseRing(N): "There is no covering module.";
  assert #Irreducibles(M) eq #Irreducibles(N);
  
  Mnew := New(GModDec);
  Mnew`group := Group(M);
  Mnew`ring := BaseRing(M);
  Mnew`irreducibles := Irreducibles(M);
  Mnew`tensors := [* Merge([*M`tensors[i], N`tensors[i]*]) : i in [1..#Irreducibles(M)]*];
  Mnew`symmetric_squares := Merge([* M`symmetric_squares, N`symmetric_squares*]);
  Mnew`restrictions := MergeAssoc([* M`restrictions, N`restrictions*]);
  
  Mnew`subspaces := [ M`subspaces[i] meet N`subspaces[i] : i in [1..#Irreducibles(M)]];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  return Mnew;
end intrinsic;

intrinsic Complement(M::GModDec, N::GModDec) -> GModDec
  {
  Returns the (G-invariant) complement of N in M.
  }
  require N subset M: "N is not a submodule of M.";
  
  Mnew := New(GModDec);
  Mnew`group := Group(M);
  Mnew`ring := BaseRing(M);
  Mnew`irreducibles := Irreducibles(M);
  Mnew`tensors := [* Merge([*M`tensors[i], N`tensors[i]*]) : i in [1..#Irreducibles(M)]*];
  Mnew`symmetric_squares := Merge([* M`symmetric_squares, N`symmetric_squares*]);
  Mnew`restrictions := MergeAssoc([* M`restrictions, N`restrictions*]);
  
  Mnew`subspaces := [ Complement(Subspace(M, i), Subspace(N, i)) : i in [1..#Irreducibles(M)]];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  return Mnew;
end intrinsic;
/*

=======  Translating between different structures  =======

*/
intrinsic GModule(M::GModDec) -> ModGrp
  {
  The magma G-module given by M.
  }
  return DirectSum(Flat([ [ Irreducibles(M)[i] : j in [1..Multiplicity(M, i)]] : i in [1..#Irreducibles(M)]]));
end intrinsic;

intrinsic VectorSpace(M::GModDec) -> ModTupRng
  {
  The vector space defined by M.
  }
  return VectorSpace(BaseRing(M), Dimension(M));
end intrinsic;
/*

=======  GModDecElts  =======

*/
intrinsic Parent(x::GModDecElt) -> GModDec
  {
  Parent of x.
  }
  return x`parent;
end intrinsic;

intrinsic Print(x::GModDecElt)
  {
  Print x.
  }
  printf "%o", x`elt;
end intrinsic;

intrinsic 'eq'(x::GModDecElt, y::GModDecElt) -> BoolElt
  {
  Equality of elements.
  }
  require Parent(x) eq Parent(y): "The two elements are not in the same module.";
  return x`elt eq y`elt;
end intrinsic;

intrinsic 'in'(x::GModDecElt, M::GModDec) -> BoolElt
  {
  Returns whether x is in M.
  }
  if Parent(x) eq M then
    return true;
  else
    return sub<Parent(x)|x> subset M;
  end if;
end intrinsic;

intrinsic Hash(x::GModDecElt) -> RngIntElt
  {
  Returns the hash value of x.
  }
  return Hash(<Parent(x), x`elt>);
end intrinsic;

intrinsic Eltseq(x::GModDecElt) -> SeqEnum
  {
  Returns the sequence of coefficients of x`elt.
  }
  return Flat([ RowSequence(x`elt[i]) : i in [1..#x`elt]]);
end intrinsic;

intrinsic Vector(x::GModDecElt) -> ModTupFld
  {
  Returns the vector.
  }
  return Vector(Flat([ RowSequence(x`elt[i]) : i in [1..#x`elt]]));
end intrinsic;

intrinsic IsZero(x::GModDecElt) -> BoolElt
  {
  Returns whether an element is zero or not.
  }
  return forall{ M : M in x`elt | IsZero(M)};
end intrinsic;

function CreateElement(M, x)
  xx := New(GModDecElt);
  xx`parent := M;
  xx`elt := x;
  return xx;
end function;

intrinsic IsCoercible(M::GModDec, x::.) -> BoolElt, GModDecElt
  {
  Returns whether x is coercible into A and the result if so.
  }
  if Type(x) eq GModDecElt and x in Generic(M) then
    return true, CreateElement(M, x`elt);
  elif Type(x) eq List and #x eq #Irreducibles(M) and
      forall{ x[i] : i in [1..#x] |
         ISA(Type(x[i]), Mtrx) and
         NumberOfColumns(x[i]) eq Dimension(Irreducibles(M)[i]) and
         NumberOfRows(x[i]) eq OverDimension(Subspace(M, i))}
   then
    return true, CreateElement(M, x);
  elif (Type(x) eq SeqEnum and #x eq OverDimension(M)) or
     (Type(x) eq ModTupFldElt and Degree(x) eq OverDimension(M)) or
     (Type(x) eq ModGrpElt and Dimension(Parent(x)) eq OverDimension(M)) then
     Mbig := Generic(M);
    seq := Partition([1..Dimension(Mbig)], [ Multiplicity(Mbig, i)*Dimension(Irreducibles(Mbig)[i]) : i in [1..#Irreducibles(Mbig)]]);
    if Type(x) in {ModTupFldElt, ModGrpElt} then
      x := Eltseq(x);
    end if;
    xx := [* Matrix(BaseRing(M), Multiplicity(Mbig, i), Dimension(Irreducibles(Mbig)[i]), x[seq[i]]) : i in [1..#seq]*];
    return true, CreateElement(M, xx);
    // Should also do for if the vectors have dim Dim(M)
  else
    return false, "Illegal coercion.";
  end if;
end intrinsic;

intrinsic Zero(M::GModDec) -> GModDecElt
  {
  Returns the zero element of M.
  }
  return CreateElement(M, [* ZeroMatrix(BaseRing(M), OverDimension(Subspace(M, i)), Dimension(Irreducibles(M)[i])) : i in [1..#Irreducibles(M)]*]);
end intrinsic;

intrinsic Basis(M::GModDec) -> SeqEnum
  {
  Basis of the module.
  }
  // Can do this quicker if needed!
  return [ M.i : i in [1..Dimension(M)]];
end intrinsic;

intrinsic '.'(M::GModDec, i::RngIntElt) -> GModDecElt
  {
  The ith basis element of the module.
  }
  require IsCoercible(Integers(), i) and 1 le i and i le Dimension(M): "This is not a valid index.";
  dims := [Dimension(Irreducibles(M)[j]) : j in [1..#Irreducibles(M)]];
  homcomps := [ Multiplicity(M, j)*dims[j] : j in [1..#Irreducibles(M)]];
  pos := [ j eq 1 select homcomps[1] else Self(j-1)+homcomps[j] : j in [1..#Irreducibles(M)]];
  
  j := Minimum({ j : j in [1..#pos] | i le pos[j]});
  
  if j eq 1 then
    offset := 0;
  else
    offset := pos[j-1];
  end if;
  
  ii := i-offset;
  ipos := (ii-1) div dims[j];
  jpos := ii-ipos*dims[j];
  x := Zero(M);
  InsertBlock(~x`elt[j], Transpose(Matrix(BasisElement(Subspace(M, j),ipos+1))), 1, jpos);
  
  return x;
end intrinsic;

intrinsic ExtendBasis(N::GModDec, M::GModDec) -> SeqEnum
  {
  Given an r-dimensional submodule N or M, return a basis of M in the form of a sequence of elements of M such that the first r elements correspond to the given basis elements for N.
  }
  C := Complement(M, N);
  Mbig := Generic(M);
  
  return [ Mbig | v : v in Basis(N)] cat [ Mbig | v : v in Basis(C)];
end intrinsic;
/*

=======  Operations on GModDecElts  =======

*/
intrinsic '+'(x::GModDecElt, y::GModDecElt) -> GModDecElt
  {
  Sums x and y.
  }
  require Generic(Parent(x)) eq Generic(Parent(y)): "x and y are not in the same module.";
  return CreateElement(Parent(x), [* x`elt[i]+y`elt[i] : i in [1..#x`elt]*]);
end intrinsic;

intrinsic '-'(x::GModDecElt) -> GModDecElt
  {
  Negation of the input.
  }
  return CreateElement(Parent(x), [* -m : m in x`elt*]);
end intrinsic;

intrinsic '-'(x::GModDecElt, y::GModDecElt) -> GModDecElt
  {
  Subtracts x and y.
  }
  require Generic(Parent(x)) eq Generic(Parent(y)): "x and y are not in the same module.";
  return CreateElement(Parent(x), [* x`elt[i]-y`elt[i] : i in [1..#x`elt]*]);
end intrinsic;

intrinsic '*'(al::RngElt, x::GModDecElt) -> GModDecElt
  {
  Returns the product of al and x.
  }
  require al in BaseRing(Parent(x)): "The scalar given is not in the base ring of the module.";
  return CreateElement(Parent(x), [* al*m : m in x`elt*]);
end intrinsic;

intrinsic '*'(x::GModDecElt, al::RngElt) -> GModDecElt
  {
  "
  }
  return al*x;
end intrinsic;

intrinsic '/'(x::GModDecElt, al::RngElt) -> GModDecElt
  {
  Returns x divided by al.
  }
  require al in BaseRing(Parent(x)): "The scalar given is not in the base ring of the module.";
  return CreateElement(Parent(x), [* m/al : m in x`elt*]);
end intrinsic;

intrinsic '*'(x::GModDecElt, g::GrpElt) -> GModDecElt
  {
  The image of x under the action of g.
  }
  M := Parent(x);
  require g in Group(M): "g is not a member of the group which acts on the module containing x.";
  // This is probably quicker than coercing each row into U, doing u*g and then reforming a matrix.  Especially as the number of rows grows.
  return CreateElement(M, [* IsZero(x`elt[i]) select x`elt[i]
                else x`elt[i]*(g@GModuleAction(Irreducibles(M)[i])) : i in [1..#x`elt] *]);
end intrinsic;

intrinsic '*'(X::SeqEnum[GModDecElt], g::GrpElt) -> SeqEnum
  {
  The image of the elements of X under the action of g.
  }
  if #X eq 0 then
    return X;
  end if;
  
  M := Parent(X[1]);
  require g in Group(M): "g is not a member of the group which acts on the module containing elements of X.";
  // This is probably quicker than coercing each row into U, doing u*g and then reforming a matrix.  Especially as the number of rows grows.
  mults := Multiplicities(M);
  mats := [* IsZero(mat) select mat
               else mat*(g@GModuleAction(Irreducibles(M)[i]))
               where mat := VerticalJoin(<x`elt[i] : x in X>) : i in [1..#mults] *];
  
  return [ CreateElement(M, [* RowSubmatrix(mats[i],[(j-1)*mults[i] +1..j*mults[i]]) : i in [1..#mults]*]) : j in [1..#X]];
end intrinsic;

intrinsic '*'(X::SetIndx[GModDecElt], g::GrpElt) -> SetIndx
  {
  The image of the elements of X under the action of g.
  }
  if #X eq 0 then
    return X;
  end if;
  
  M := Parent(X[1]);
  require g in Group(M): "g is not a member of the group which acts on the module containing elements of X.";
  // This is probably quicker than coercing each row into U, doing u*g and then reforming a matrix.  Especially as the number of rows grows.
  mults := Multiplicities(M);
  mats := [* IsZero(mat) select mat
               else mat*(g@GModuleAction(Irreducibles(M)[i]))
               where mat := VerticalJoin(<x`elt[i] : x in X>) : i in [1..#mults] *];
  
  return {@ CreateElement(M, [* RowSubmatrix(mats[i],[(j-1)*mults[i] +1..j*mults[i]]) : i in [1..#mults]*]) : j in [1..#X]@};
end intrinsic;
