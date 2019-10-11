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
  irreducibles,       // A SeqEnum of all the irreducibles for the group G
  multiplicities,     // A SeqEnum of the multiplicities of each irreducible
  subspaces,          // A SeqEnum of vector spaces of the corresponding multiplicity
  tensors,            // A List of Lists of tuples <S, iso>, where S lists the multiplicities of the irreducibles in the tensor product and iso is an isomorphism from the tensor product in the normal sense, to our decomposed version.
  symmetric_squares;  // A List <S, iso>, where S lists the multiplicities of the irreducibles in the symmetric square and iso is an isomorphism from the symmetric square in the normal sense, to our decomposed version.
 
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
  printf "A DecomposedGModule of dimension %o over %o", Dimension(M), BaseRing(M);
end intrinsic;

intrinsic Group(M::GModDec) -> Grp
  {
  The group G of the G-module M.
  }
  return M`group;
end intrinsic;

intrinsic Dimension(M::GModDec) -> RngIntElt
  {
  Dimension of the module.
  }
  return forall{m : m in M`multiplicities | m eq 0} select 0 else 
         &+[ M`multiplicities[i]*Dimension(M`irreducibles[i]) : i in [1..#M`multiplicities] | M`multiplicities[i] ne 0];
end intrinsic;

intrinsic OverDimension(M::GModDec) -> RngIntElt
  {
  Dimension of the full module containing M.
  }
  dims := [OverDimension(V) : V in M`subspaces];
  return forall{m : m in dims | m eq 0} select 0 else 
         &+[ dims[i]*Dimension(M`irreducibles[i]) : i in [1..#M`irreducibles] | dims[i] ne 0];
end intrinsic;

intrinsic BaseRing(M::GModDec) -> Rng
  {
  Base ring of the module.
  }
  return BaseRing(M`irreducibles[1]);
end intrinsic;

intrinsic ConstituentSupport(M::GModDec) -> SeqEnum
  {
  The indices of the irreducibles which M is supported on.
  }
  return [ i : i in [1..#M`irredicubles] | M`multiplicities[i] ne 0];
end intrinsic;

intrinsic GModuleAction(M::GModDec) -> Map
  {
  Returns the action homomorphism of M
  }
  return hom< Group(M) -> GL(Dimension(M), BaseRing(M)) | g:-> DiagonalJoin(< g@GModuleAction(M`irreducibles[i]) : j in [1..M`multiplicities[i]], i in [1..#M`irreducibles]>)>;  
end intrinsic;
/*

=======  Creating a GModDecs  =======

*/
intrinsic DecomposedGModule(M::GModDec) -> GModDec, AlgMatElt
  {
  The GModDec of the magma G-module M.
  }
  return M, IdentityMatrix(BaseRing(M), Dimension(M));
end intrinsic;

intrinsic DecomposedGModule(M::ModGrp) -> GModDec, AlgMatElt
  {
  The GModDec of the magma G-module M.
  }
  G := Group(M);
  F := BaseRing(M);
  
  N := New(GModDec);
  N`group := G;
  N`irreducibles := IrreducibleModules(G, F);
  
  if F eq Rationals() then
    T := RationalCharacterTable(G);
    char := Character(M);
    N`multiplicities := ChangeUniverse(Decomposition(T, char), Integers());
    dec := Decomposition(M);
    // NB the decomposition may not be in order of T
    Sort(~dec, func<A,B | Position(T,Character(A)) - Position(T, Character(B))>);
  else
    dec := Decomposition(M);
    iso_class := {* i where so := exists(i){i : i in [1..#N`irreducibles] | IsIsomorphic(U, N`irreducibles[i])} : U in dec *};
    N`multiplicities := ChangeUniverse([ Multiplicity(iso_class, i) : i in [1..#N`irreducibles]], Integers());
  end if;
    
  N`subspaces := [ VectorSpace(F, d) : d in N`multiplicities ];

  N`tensors := [* [* false : j in [1..#N`irreducibles]*] : i in [1..#N`irreducibles]*];
  N`symmetric_squares := [* false : i in [1..#N`irreducibles]*];
  
  S := Sort(MultisetToSequence({* i^^N`multiplicities[i] : i in [1..#N`irreducibles]*}));
  CoB := Matrix([ VectorSpace(M) | M!u : u in Basis(U), U in dec])^-1 *
           DiagonalJoin(< iso where so, iso := IsIsomorphic(dec[i], N`irreducibles[S[i]]) : i in [1..#dec]>);
  
  return N, CoB;
end intrinsic;

intrinsic DecomposedGModule(S::SeqEnum[Mtrx]) -> GModDec
  {
  Returns the decomposed G-module generated by the matrices in S.
  }
  // NOT YET IMPLMENTED
  // return null;
end intrinsic;
/*

=======  Building new GModDecs out of old ones  =======

*/
intrinsic SubConstructor(M::GModDec, X::.) -> GModDec
  {
  The submodule generated by X.
  }
  if #X eq 1 and Type(X[1]) in {SeqEnum, SetEnum, SetIndx} and forall{x : x in X[1] | Type(x) in { GModDecElt, SeqEnum, ModTupFldElt, ModGrpElt}} then
    X := X[1];
  end if;
  XX := { M | x : x in X };
  
  Mnew := New(GModDec);
  Mnew`group := M`group;
  Mnew`irreducibles := M`irreducibles;
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  
  if #XX eq 0 then
    Mnew`subspaces := [ sub< Generic(M`subspaces[i]) |> : i in [1..#M`irreducibles]];
  else
    // We want to take the column span of each element
    Mnew`subspaces := [ sub< Generic(M`subspaces[i]) | Flat([ Rows(Transpose(x`elt[i])) : x in XX])> : i in [1..#M`irreducibles]];
  end if;
  
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  return Mnew;
end intrinsic;
/*

Given a sequence of maps Q, one for each homogeneous component of a GModDec N, returns the matrix for the map from N to M

*/
function CompMapsToFullMap(N, M, L);
  F := BaseRing(N);
  irredbas := < N`multiplicities[i] eq 0 select ZeroMatrix(F, 0,Dimension(N`irreducibles[i])) else BasisMatrix(VectorSpace(N`irreducibles[i])) : i in [1..#N`irreducibles]>;
  maps := < Dimension(Domain(L[i])) eq 0 select ZeroMatrix(F, 0, Dimension(Codomain(L[i]))) else Dimension(Image(L[i])) eq 0 select ZeroMatrix(F, Dimension(Domain(L[i])), 0) else Matrix([v@L[i] : v in Basis(Domain(L[i]))]) : i in [1..#L] >;
  mat := DiagonalJoin(< TensorProduct(maps[i], irredbas[i]) : i in [1..#L]>);
  return mat;
  // Want to make this a map, but can't do so in a way which allows MapToMatrix after
  // Something about not a reduced module??
  // return hom< VectorSpace(N) -> VectorSpace(M) | mat>;
end function;

intrinsic QuoConstructor(M::GModDec, X::.) -> GModDec, SeqEnum[Map]
  {
  The quotient of M by the submodule generated by X and also a sequence of quotient maps.
  }
  if #X eq 1 and Type(X[1]) eq SeqEnum and forall{x : x in X[1] | Type(x) in { GModDecElt, SeqEnum, ModTupFldElt, ModGrpElt}} then
    X := X[1];
  elif #X eq 1 and Type(X[1]) eq GModDec and X[1] subset M then
    X := Basis(X[1]);
  end if;
  XX := { M | x : x in X };
  
  Mnew := New(GModDec);
  Mnew`group := M`group;
  Mnew`irreducibles := M`irreducibles;
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  
  quos := [ < Q, psi> where Q, psi := quo< M`subspaces[i] | Flat([ Rows(Transpose(x`elt[i])) : x in XX])> : i in [1..#M`irreducibles]];
  
  Mnew`subspaces := [ t[1] : t in quos];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  return Mnew, CompMapsToFullMap(M, Mnew, [ t[2] : t in quos]);
end intrinsic;

intrinsic QuoMap(M::GModDec, X::.) -> Mtrx
  {
  The quotient of M by the submodule generated by X and also a sequence of quotient maps.
  }
  if Type(X) eq GModDec and X subset M then
    X := Basis(X);
  end if;
  XX := { M | x : x in X };
  
  Mnew := New(GModDec);
  Mnew`group := M`group;
  Mnew`irreducibles := M`irreducibles;
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  
  quos := [ < Q, psi> where Q, psi := quo< M`subspaces[i] | Flat([ Rows(Transpose(x`elt[i])) : x in XX])> : i in [1..#M`irreducibles]];
  
  Mnew`subspaces := [ t[1] : t in quos];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  return CompMapsToFullMap(M, Mnew, [ t[2] : t in quos]);
end intrinsic;

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


intrinsic DirectSum(M::GModDec, N::GModDec) -> GModDec, AlgMatElt, AlgMatElt, AlgMatElt, AlgMatElt
  {
  The direct sum of M and N, the two inclusion maps and the two projection maps.
  }
  F := BaseRing(M);
  require Group(M) eq Group(N) and F eq BaseRing(N): "The two modules must be for the same group and over the same field.";
  Mnew := New(GModDec);
  Mnew`group := M`group;
  Mnew`irreducibles := M`irreducibles;
  
  Mnew`tensors := [* Merge([*M`tensors[i], N`tensors[i]*]) : i in [1..#M`irreducibles]*];
  Mnew`symmetric_squares := Merge([* M`symmetric_squares, N`symmetric_squares*]);
  
  sums := [ < V, inj1, inj2, proj1, proj2 > 
      where V, inj1, inj2, proj1, proj2 := DirectSum(M`subspaces[i], N`subspaces[i])
                   : i in [1..#M`irreducibles]];
  
  Mnew`subspaces := [ t[1] : t in sums ];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  inj1, proj1 := Explode(< CompMapsToFullMap(M, Mnew, [t[i] : t in sums ]) : i in [2,4]>);
  inj2, proj2 := Explode(< CompMapsToFullMap(N, Mnew, [t[i] : t in sums ]) : i in [3,5]>);

  // Don't know how to form maps between objects of our new type
  // Can magma even do this???
  // For now, we return a sequence of matrices.  Should really turn them back to maps to match ModGrp and MudTupFld, but we will use matrices anyway.
  return Mnew, inj1, inj2, proj1, proj2;
end intrinsic;

intrinsic DirectSum(Q::SeqEnum[GModDec]) -> GModDec, SeqEnum, SeqEnum
  {
  The direct sum of the modules in Q, a sequence of inclusion maps and a sequence of projection maps given as matrices.
  }
  require #Q ne 0: "The sequence of Gmodules for the direct sum is empty.";
  F := BaseRing(Q[1]);
  
  require forall{ M : M in Q | Group(M) eq Group(Q[1])} and forall{ M : M in Q | BaseRing(M) eq F}: "The modules must be for the same group and over the same field.";
  Mnew := New(GModDec);
  Mnew`group := Q[1]`group;
  Mnew`irreducibles := Q[1]`irreducibles;
  
  Mnew`tensors := [* Merge([*M`tensors[i] : M in Q*]) : i in [1..#Mnew`irreducibles]*];
  Mnew`symmetric_squares := Merge([* M`symmetric_squares : M in Q*]);
  
  // NB need to use VectorSpace here as otherwise the direct sum takes the ambient space of a subspace rather than the subspace itself.
  sums := [ < V, injs, projs > 
      where V, injs, projs := DirectSum([ VectorSpace(F, Dimension(M`subspaces[i])) : M in Q])
                   : i in [1..#Mnew`irreducibles]];
  
  Mnew`subspaces := [ t[1] : t in sums ];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  injs := < CompMapsToFullMap(Q[i], Mnew, [t[2,i] : t in sums]) : i in [1..#Q]>;
  projs := < CompMapsToFullMap(Q[i], Mnew, [t[3,i] : t in sums]) : i in [1..#Q]>;
  // Don't know how to form maps between objects of our new type
  // Can magma even do this???
  // For now, we return a sequence of matrices.  Should really turn them back to maps to match ModGrp and MudTupFld, but we will use matrices anyway.
  return Mnew, injs, projs;
end intrinsic;

/*

Given a GModDec M, return the tensor product of the ith and jth irreducibles, calculating and caching it if necessary.

Same for symmetric square

*/
// NB we are only caching the result on M, not N
function GetTensor(M, i, j)
  t := Cputime();
  
  if j lt i then
    // only calculate the isomorphism one way round
    S, iso := GetTensor(M, j, i);
    seq := [ [k,l] : k in [1..Dimension(M`irreducibles[i])], l in [1..Dimension(M`irreducibles[j])]];
    Sort(~seq, ~perm);
    P := PermutationMatrix(BaseRing(M), perm);
    
    isorev := P*iso;
    return S, isorev;
  end if;
  
  if Type(M`tensors[i,j]) eq BoolElt then
    vprint GModDec, 2: "Calculating tensor.";
    /*
    UxV := TensorProduct(M`irreducibles[i], M`irreducibles[j]);
  
    // I think using characters will be quicker  
    if BaseRing(M) eq Rationals() then
      T := RationalCharacterTable(Group(M));
      char := Character(UxV);
      S := ChangeUniverse(Decomposition(T, char), Integers());
      SS := Sort(MultisetToSequence({* i^^S[i] : i in [1..#M`irreducibles]*}));
    else
      dec := Decomposition(UxV);
      SS := Sort(MultisetToSequence({* i where so := exists(i){i : i in [1..#M`irreducibles] | IsIsomorphic(U, M`irreducibles[i])} : U in dec *}));
      S := [ Multiplicity(SS,i) : i in [1..#M`irreducibles]];
    end if;
    
    N := DirectSum([ M`irreducibles[i] : i in SS]);
    tt := Cputime();
    so, iso := IsIsomorphic(UxV, N);
    vprintf GModDec, 4: "Time taken for isomorphic method: %o.\n", Cputime(tt);
    
    delete UxV;
    */
    UxV := TensorProduct(M`irreducibles[i], M`irreducibles[j]);
    // I think using characters will be quicker  
    if BaseRing(M) eq Rationals() then
      T := RationalCharacterTable(Group(M));
      char := Character(UxV);
      S := ChangeUniverse(Decomposition(T, char), Integers());
      SS := Sort(MultisetToSequence({* i^^S[i] : i in [1..#M`irreducibles]*}));
    else
      dec := Decomposition(UxV);
      SS := Sort(MultisetToSequence({* i where so := exists(i){i : i in [1..#M`irreducibles] | IsIsomorphic(U, M`irreducibles[i])} : U in dec *}));
      S := [ Multiplicity(SS,i) : i in [1..#M`irreducibles]];
    end if;
    
    N := DirectSum([ M`irreducibles[i] : i in SS]);
    
    tt := Cputime();
    inds := IndecomposableSummands(UxV);
    T := RationalCharacterTable(Group(M));
    charpos := [Position(T,Character(U)) : U in inds];
    Sort(~charpos, ~perm);
    inds := PermuteSequence(inds, perm);
    iso := VerticalJoin(< hom*Matrix([UxV!u : u in Basis(inds[i])]) where _, hom := IsIsomorphic(M`irreducibles[charpos[i]], inds[i]) : i in [1..#charpos]>)^-1;
    vprintf GModDec, 4: "Time taken for indecomposables method: %o.\n", Cputime(tt);
    
    //assert so;
    //assert3 forall(err){ <i,g> : g in Generators(Group(UxV)), i in [1..Dimension(UxV)] | N!Eltseq(((UxV.i)*g)*mat) eq (N!Eltseq((UxV.i)*mat))*g};
    
    M`tensors[i,j] := <S, iso>;
  else
     vprint GModDec, 2: "Tensor already cached.";
  end if;
  vprintf GModDec, 4: "Time taken: %o.\n", Cputime(t);
  
  return M`tensors[i,j,1], M`tensors[i,j,2];
end function;

function GetS2(M, i)
  t := Cputime();
  if Type(M`symmetric_squares[i]) eq BoolElt then
    vprint GModDec, 2: "Calculating symmetric square.";
    S2 := SymmetricSquare(M`irreducibles[i]);
  
    if BaseRing(M) eq Rationals() then
      T := RationalCharacterTable(Group(M));
      char := Character(S2);
      S := ChangeUniverse(Decomposition(T, char), Integers());
      SS := Sort(MultisetToSequence({* i^^S[i] : i in [1..#M`irreducibles]*}));
    else
      dec := Decomposition(S2);
      SS := Sort(MultisetToSequence({* i where so := exists(i){i : i in [1..#M`irreducibles] | IsIsomorphic(U, M`irreducibles[i])} : U in dec *}));
      S := [ Multiplicity(SS,i) : i in [1..#M`irreducibles]];
    end if;
    
    N := DirectSum([ M`irreducibles[i] : i in SS]);
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

Given two irreducibles U, V, we have already calculated their tensor UxV and an isomorphism iso onto our copy of this which is isomorphic to a direct sum of the contituents of UxV in order.

Suppose that we are doing the tensor of M and N where U \subset M and V subset N.  Then, MxN has the constituents of UxV in some order.

This function gives the image of UxV in our copy of MxN, where S is the list of mulitplicities of irreducibles in UxV and pos is a sequence of sequences [ T_1,..., T_n] where T_k describes the positions in MxN of the kth irreducible in UxV and mult is the multiplicites of the irreducibles in MxN and dims the dimensions of the irreducibles.

*/
function TensorConvert(iso, S, pos, dims, mult)
  // We find how to chop up the images in iso to map onto the homogeneuos components.
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
  // Now we must app the last one as well
  Append(~zerodims, num);
  
  assert &+zerodims + dim eq &+[mult[i]*dims[i] : i in [1..#mult]];
  assert #zerodims eq #isoparts+1;
  
  F := BaseRing(iso);
  return HorizontalJoin(< IsOdd(i) select ZeroMatrix(F, dim, zerodims[(i+1) div 2]) else isoparts[i div 2] : i in [1..2*#isoparts+1]>);
end function;

intrinsic TensorProduct(M::GModDec, N::GModDec) -> GModDec, SeqEnum
  {
  The tensor product of M and N.
  }
  require Group(M) eq Group(N) and BaseRing(M) eq BaseRing(N): "The two modules must be for the same group and over the same field.";
  vprint GModDec, 2: "Calculating the GModDec tensor product.";
  
  t := Cputime();  
  if Dimension(M) eq 0 or Dimension(N) eq 0 then
    return sub<M|>, _;
  end if;
  
  no_const := #M`irreducibles;
  
  // We form a sequence of the indices of the irreducibles, taking acount of their multiplicities.
  irreds_M := Sort(MultisetToSequence({* i^^M`multiplicities[i] : i in [1..no_const]*}));
  irreds_N := Sort(MultisetToSequence({* i^^N`multiplicities[i] : i in [1..no_const]*}));
  
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
  Mnew`group := M`group;
  Mnew`irreducibles := M`irreducibles;
  
  Mnew`tensors := [* Merge([*M`tensors[i], N`tensors[i]*]) : i in [1..no_const]*];
  Mnew`symmetric_squares := Merge([* M`symmetric_squares, N`symmetric_squares*]);
  
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
ijpos := function(i,j,n)
  if i le j then
    return &+[ n+1 -k : k in [0..i-1]] -n +j-i;
  else
    return &+[ n+1 -k : k in [0..j-1]] -n +i-j;
  end if;
end function;

intrinsic SymmetricSquare(M::GModDec) -> GModDec, SeqEnum
  {
  The symmetric square of M.
  }
  if Dimension(M) eq 0 then
    return M, _;
  end if;
  vprint GModDec, 2: "Calculating the GModDec tensor product.";
  t := Cputime();  

  no_const := #M`irreducibles;
  
  // We form a sequence of the indices of the irreducibles, taking acount of their multiplicities.
  irreds_M := Sort(MultisetToSequence({* i^^M`multiplicities[i] : i in [1..no_const]*}));
  
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
  Mnew`group := M`group;
  Mnew`irreducibles := M`irreducibles;
  
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  
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

intrinsic Restriction(M::GModDec, H::Grp) -> GModDec
  {
  Returns the restriction of the G-module M to an H-module where H is a subgroup of G.
  }
  // NOT YET IMPLMENTED
  // return null;
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
  The column moduli of the module M over a euclidean domain.
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
  Mnew`group := M`group;
  Mnew`irreducibles := M`irreducibles;
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  
  Mnew`subspaces := [ Generic(V) : V in M`subspaces ];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  return Mnew;
end intrinsic;

intrinsic 'eq'(M::GModDec, N::GModDec) -> BoolElt
  {
  Equality of two submodules M and N.
  }
  require M`group eq N`group and BaseRing(M) eq BaseRing(N): "There is no covering module.";
  assert #M`irreducibles eq # N`irreducibles;
  
  return forall{ i : i in [1..#M`irreducibles] | M`subspaces[i] eq N`subspaces[i]};
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
  require M`group eq N`group and BaseRing(M) eq BaseRing(N): "There is no covering module.";
  assert #M`irreducibles eq # N`irreducibles;
  
  return forall{ i : i in [1..#N`irreducibles] | N`subspaces[i] subset M`subspaces[i]};
end intrinsic;

intrinsic '+'(M::GModDec, N::GModDec) -> GModDec
  {
  The sum of the two submodules M and N.
  }
  require M`group eq N`group and BaseRing(M) eq BaseRing(N): "There is no covering module.";
  assert #M`irreducibles eq # N`irreducibles;
  
  Mnew := New(GModDec);
  Mnew`group := M`group;
  Mnew`irreducibles := M`irreducibles;
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  
  Mnew`subspaces := [ M`subspaces[i] + N`subspaces[i] : i in [1..#M`irreducibles]];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  return Mnew;
end intrinsic;

intrinsic 'meet'(M::GModDec, N::GModDec) -> GModDec
  {
  The intersection of two submodules M and N.
  }
  require M`group eq N`group and BaseRing(M) eq BaseRing(N): "There is no covering module.";
  assert #M`irreducibles eq # N`irreducibles;
  
  Mnew := New(GModDec);
  Mnew`group := M`group;
  Mnew`irreducibles := M`irreducibles;
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  
  Mnew`subspaces := [ M`subspaces[i] meet N`subspaces[i] : i in [1..#M`irreducibles]];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  return Mnew;
end intrinsic;

intrinsic Complement(M::GModDec, N::GModDec) -> GModDec
  {
  Returns the (G-invariant) complement of N in M.
  }
  require N subset M: "N is not a submodule of M.";
  
  Mnew := New(GModDec);
  Mnew`group := M`group;
  Mnew`irreducibles := M`irreducibles;
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  
  Mnew`subspaces := [ Complement(M`subspaces[i], N`subspaces[i]) : i in [1..#M`irreducibles]];
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
  return DirectSum(Flat([ [ M`irreducibles[i] : j in [1..M`multiplicities[i]]] : i in [1..#M`irreducibles]]));
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
  require x`parent eq y`parent: "The two elements are not in the same module.";
  return x`elt eq y`elt;
end intrinsic;

intrinsic 'in'(x::GModDecElt, M::GModDec) -> BoolElt
  {
  Returns whether x is in M.
  }
  if x`parent eq M then
    return true;
  else
    return sub<x`parent|x> subset M;
  end if;
end intrinsic;

intrinsic Hash(x::GModDecElt) -> RngIntElt
  {
  Returns the hash value of x.
  }
  return Hash(<Group(x`parent), x`elt>);
end intrinsic;

// Is this really needed?
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
  elif Type(x) eq List and #x eq #M`irreducibles and
      forall{ x[i] : i in [1..#x] |
         ISA(Type(x[i]), Mtrx) and
         NumberOfColumns(x[i]) eq Dimension(M`irreducibles[i]) and
         NumberOfRows(x[i]) eq OverDimension(M`subspaces[i])}
   then
    return true, CreateElement(M, x);
  elif (Type(x) eq SeqEnum and #x eq OverDimension(M)) or
     (Type(x) eq ModTupFldElt and Degree(x) eq OverDimension(M)) or
     (Type(x) eq ModGrpElt and Dimension(Parent(x)) eq OverDimension(M)) then
     Mbig := Generic(M);
    seq := Partition([1..Dimension(Mbig)], [ Mbig`multiplicities[i]*Dimension(Mbig`irreducibles[i]) : i in [1..#Mbig`multiplicities]]);
    if Type(x) in {ModTupFldElt, ModGrpElt} then
      x := Eltseq(x);
    end if;
    xx := [* Matrix(BaseRing(M), Mbig`multiplicities[i], Dimension(Mbig`irreducibles[i]), x[seq[i]]) : i in [1..#seq]*];
    return true, CreateElement(M, xx);
    // Should also do for if the vectors if dim Dim(M)
  else
    return false, "Illegal coercion.";
  end if;
end intrinsic;

intrinsic Zero(M::GModDec) -> GModDecElt
  {
  Returns the zero element of M.
  }
  return CreateElement(M, [* ZeroMatrix(BaseRing(M), OverDimension(M`subspaces[i]), Dimension(M`irreducibles[i])) : i in [1..#M`irreducibles]*]);
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
  dims := [Dimension(M`irreducibles[j]) : j in [1..#M`irreducibles]];
  homcomps := [ M`multiplicities[j]*dims[j] : j in [1..#M`irreducibles]];
  pos := [ j eq 1 select homcomps[1] else Self(j-1)+homcomps[j] : j in [1..#M`irreducibles]];
  
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
  InsertBlock(~x`elt[j], Transpose(Matrix(BasisElement(M`subspaces[j],ipos+1))), 1, jpos);
  
  return x;
end intrinsic;

intrinsic ExtendBasis(N::GModDec, M::GModDec) -> SeqEnum
  {
  Given an r-dimensional submodule N or M, return a basis of M in the form of a ssequence of elements of M such that the first r elements correspond to the given basis elements for N.
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
  return CreateElement(M, [* x`elt[i]*(g@GModuleAction(M`irreducibles[i])) : i in [1..#x`elt] *]);
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
  mats := [* VerticalJoin(<x`elt[i] : x in X>)*(g@GModuleAction(M`irreducibles[i])) : i in [1..#M`irreducibles] *];
  mults := [ M`multiplicities[i] : i in [1..#M`irreducibles]];
  
  return [ CreateElement(M, [* RowSubmatrix(mats[i],[(j-1)*mults[i] +1..j*mults[i]]) : i in [1..#M`irreducibles]*]) : j in [1..#X]];
end intrinsic;

intrinsic '*'(X::SetIndx[GModDecElt], g::GrpElt) -> SeqEnum
  {
  The image of the elements of X under the action of g.
  }
  if #X eq 0 then
    return X;
  end if;
  
  M := Parent(X[1]);
  require g in Group(M): "g is not a member of the group which acts on the module containing elements of X.";
  // This is probably quicker than coercing each row into U, doing u*g and then reforming a matrix.  Especially as the number of rows grows.
  mats := [* VerticalJoin(<X[j]`elt[i] : j in [1..#X]>) *(g@GModuleAction(M`irreducibles[i])) : i in [1..#M`irreducibles] *];
  mults := [ M`multiplicities[i] : i in [1..#M`irreducibles]];
  
  return {@ CreateElement(M, [* RowSubmatrix(mats[i],[(j-1)*mults[i] +1..j*mults[i]]) : i in [1..#M`irreducibles]*]) : j in [1..#X]@};
end intrinsic;
// I have no idea how to define maps for a new class of object!!
/*
intrinsic '@'(x::GModDecElt, psi::Map) -> GModDecElt
{}
  return Parent(x)!(Vector(x)*psi);
end intrinsic;
*/
