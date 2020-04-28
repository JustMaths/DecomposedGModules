/*

Maps between GModDecs

*/
declare type GModDecHom;

declare attributes GModDecHom:
  domain,           // A GModDec giving the domain
  codomain,         // A GModDec giving the codomain
  maps;             // A List of vector space homomorphisms representing the maps

declare type GModDecBil;

/*
Let A = \bigoplus_i S_i \otimes U_i
    B = \bigoplus_i T_i \otimes U_i
    C = \bigoplus_i Z_i \otimes U_i

And U_i \otimes U_j = \bigoplus_k R_k \otimes U_k

For each i,j,k we have a tensor:
  R_k \otimes S_i \otimes T_j \to Z_k
  
NB this is stored as f`maps[i,j,k].  Note the difference in indexing.
*/
declare attributes GModDecBil:
  domain,           // A List of two GModDecs A, B giving the domain
  codomain,         // A GModDec C giving the codomain
  maps;             // A List of Lists of Lists of tensors as above

import "GModDec.m": CreateElement;
/*

======== Basic properties of maps ========

*/
intrinsic Print(f::GModDecHom)
  {
  Prints a GModDecHom.
  }
  printf "Homomorphism from: %o to %o", Domain(f), Codomain(f);
end intrinsic;

intrinsic Domain(f::GModDecHom) -> GModDec
  {
  The domain of the map f.
  }
  return f`domain;
end intrinsic;

intrinsic Codomain(f::GModDecHom) -> GModDec
  {
  The Coomain of the map f.
  }
  return f`codomain;
end intrinsic;

intrinsic Image(f::GModDecHom) -> GModDec
  {
  The image of the map f.
  }
  ims := [ Image(f`maps[i]) : i in [1..#f`maps]];
  return sub<Codomain(f) | ims>;
end intrinsic;

intrinsic Kernel(f::GModDecHom) -> GModDec
  {
  The kernel of the map f.
  }
  kers := [ Kernel(f`maps[i]) : i in [1..#f`maps]];
  return sub<Domain(f) | kers>;
end intrinsic;

intrinsic IsIdentity(f::GModDecHom) -> BoolElt
  {
  Is the map the identity homomorphism?
  }
  // NOT YET IMPLMENTED
  // return null;
end intrinsic;
/*

======== Creating a GModDecHom ========

*/

// function to create the maps
function CreateMap(dom, cod, maps)
  f := New(GModDecHom);
  f`domain := dom;
  f`codomain := cod;
  f`maps := maps;
  return f;
end function;

// Really want to use the hom constructor here, but this isn't currently possible in magma
intrinsic DecomposedGModuleHomomorphism(M::GModDec, N::GModDec, S::[Map]) -> GModDecHom
  {
  Create a homomorphism between M and N given by a sequence of maps.
  }
  require BaseRing(M) eq BaseRing(N) and Group(M) eq Group(N): "The domain and image modules are not compatible.";
  require #S eq #Irreducibles(M): "The number of maps given is not correct.";
  require forall{ i : i in [1..#Irreducibles(M)] | Domain(S[i]) eq Subspace(M, i)}: "The domains of the given maps are not the homogeneous components of the given domain module.";
  require forall{ i : i in [1..#Irreducibles(N)] | Codomain(S[i]) subset Generic(Subspace(N, i))}: "The codomains of the given maps are not contained in the homogeneous components of the given image module.";
  // There is a bug with magma not giving the correct image for a map which is the composite of two maps.
  require forall{ i : i in [1..#Irreducibles(N)] | sub<Image(S[i])|[v@S[i] : v in Basis(Domain(S[i]))]> subset Subspace(N, i)}: "The image of the given maps are not contained in the homogeneous components of the given image module.";
  return CreateMap(M, N, S);
end intrinsic;

intrinsic Hom(M::GModDec, N::GModDec, S::[Map]) -> GModDecHom
  {
  "
  }
  return DecomposedGModuleHomomorphism(M, N, S);
end intrinsic;
/*

======== New maps from old ========

*/
intrinsic '*'(f::GModDecHom, g::GModDecHom) -> GModDecHom
  {
  Composition of f and g.
  }
  require Image(f) subset g`domain: "The image of one map is not contained in the domain of the other.";
  return CreateMap(Domain(f), Codomain(g), [ f`maps[i]*g`maps[i] : i in [1..#Irreducibles(Domain(f))]]);
end intrinsic;

intrinsic Inverse(f::GModDecHom) -> GModDecHom
  {
  The inverse of f.
  }
  invs := [ Inverse(f`maps[i]) : i in [1..#f`maps]];
  return CreateMap(Image(f), Domain(f), invs);
end intrinsic;
/*

======== Application of a map ========

*/
intrinsic '@'(m::GModDecElt, f::GModDecHom) -> GModDecElt
  {
  Apply f to m.
  }
  require m in Domain(f): "The element is not in the domain of the map.";
  M := Parent(m);
  N := Generic(Codomain(f));
  ff := [* Transpose(Matrix(BaseRing(M), Multiplicity(M, i), Multiplicity(N, i),
                  [ Subspace(M, i).j@f`maps[i] : j in [1..Dimension(Subspace(M, i))]]))
               : i in [1..#Irreducibles(M)] *];
  
  // We might be trying to apply the zero map and then we get incompatible degrees
  apply_matrix := function(mat, x)
    try
      return mat*x;
    catch e
      assert IsZero(x);
      return ZeroMatrix(BaseRing(M), NumberOfRows(mat), NumberOfColumns(x));
    end try;  
  end function;
  
  xx := [* apply_matrix(ff[i], m`elt[i]) : i in [1..#f`maps] *];
  return CreateElement(Codomain(f), xx);
end intrinsic;

intrinsic '@'(S::[GModDecElt], f::GModDecHom) -> SeqEnum
  {
  Apply f to the sequence S.
  }
  // Could be done faster if needed.
  return [ m@f : m in S];
end intrinsic;

intrinsic '@'(S::{@GModDecElt@}, f::GModDecHom) -> SetIndx
  {
  Apply f to the indexed set S.
  }
  // Could be done faster if needed.
  return {@ m@f : m in S@};
end intrinsic;

intrinsic '@'(S::{GModDecElt}, f::GModDecHom) -> SetEnum
  {
  Apply f to the set S.
  }
  // Could be done faster if needed.
  return { m@f : m in S};
end intrinsic;

intrinsic '@'(M::GModDec, f::GModDecHom) -> GModDec
  {
  Apply f to M.
  }
  require Group(M) eq Group(Domain(f)) and BaseRing(M) eq BaseRing(Domain(f)): "The module is not in the domain of the map.";

  Mnew := New(GModDec);
  Mnew`group := Group(M);
  Mnew`ring := BaseRing(M);
  Mnew`irreducibles := Irreducibles(M);
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  Mnew`restrictions := M`restrictions;

  Mnew`subspaces := [ Subspace(M, i)@f`maps[i] : i in [1..#f`maps]];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  return Mnew;
end intrinsic;

// Do preimages??

/*

======== Translation into a matrix ========

*/
intrinsic MapToMatrix(f::GModDecHom) -> ModMatFldElt
  {
  Return the matrix given by the map f.
  }
  M := Domain(f);
  F := BaseRing(M);
  
  irredbas := < Multiplicity(M, i) eq 0 select ZeroMatrix(F, 0, Dimension(Irreducibles(M)[i]))
                 else BasisMatrix(VectorSpace(Irreducibles(M)[i]))
                    : i in [1..#Irreducibles(M)]>;
  maps := < Dimension(Domain(f`maps[i])) eq 0 select ZeroMatrix(F, 0, Dimension(Image(f`maps[i])))
             else Dimension(Image(f`maps[i])) eq 0 select ZeroMatrix(F, Dimension(Domain(f`maps[i])), 0)
             else Matrix([v@f`maps[i] : v in Basis(Domain(f`maps[i]))])
                : i in [1..#f`maps] >;
  mat := DiagonalJoin(< TensorProduct(maps[i], irredbas[i]) : i in [1..#f`maps]>);
  return mat;
end intrinsic;
/*

======== GModDecBil =========

*/
intrinsic Print(f::GModDecBil)
  {
  Prints a GModDecBil.
  }
  printf "Bilinear map from: %o and %o to %o", Domain(f)[1], Domain(f)[2], Codomain(f);
end intrinsic;

intrinsic Domain(f::GModDecBil) -> GModDec
  {
  Domain of f.
  }
  return f`domain;
end intrinsic;

intrinsic Codomain(f::GModDecBil) -> GModDec
  {
  Codomain of f.
  }
  return f`codomain;
end intrinsic;

intrinsic Image(f::GModDecBil) -> GModDec
  {
  The image of the map f.
  }
  // NOT YET IMPLMENTED
  // return null;
end intrinsic;

intrinsic SubmoduleImage(M::GModDec, N::GModDec, f::GModDecBil) -> GModDec
  {
  Given a bilinear map f: A \otimes B -> C and submodules M \leq A and N \leq B, return the submodule f(M, N).
  }
  require M subset Domain(f)[1] and N subset Domain(f)[2]: "The modules are not elements of the domain of the bilinear map.";
  
  C := Codomain(f);
  
  Im := [ PowerStructure(Type(M`subspaces[1])) | ];
  for k in [1..#Multiplicities(C)] do
    Z := C`subspaces[k];
    // We take the subspaces S_i and T_j and decompose our tensor
    Zs := [ Parent(Z) |];
    for i in [1..#Multiplicities(M)], j in [1..#Multiplicities(N)] do
      // Find the d = Dimension(S)*Dimension(T) matrices corresponding to the maps M in Hom(R \otimes Z, F^d)
      mats := AsMatrices(f`maps[i,j,k], 3, 0);
      
      if #mats eq 0 then
        continue;
      end if;
      ST := TensorProduct(Subspace(M, i), Subspace(N, j));
      
      // Can do this quicker with matrices          
      Append(~Zs, sub<Z | &cat[Rows(&+[ st[l]*mats[l] : l in [1..#mats]]) : st in Basis(ST)]>);
    end for;
    Zs := &+Zs;
    
    Append(~Im, Zs);
  end for;
  
  return sub< C | Im>;
end intrinsic;

intrinsic AdjointAction(f::GModDecBil, a::GModDecElt) -> GModDecHom
  {
  Given a bilinear map from A \otimes B -> C and an element a of A, we give a map from B to C given by the adjoint action of a.  That is, the action x \maptso a \otimes x.
  }
  dom := Domain(f);
  require a in dom[1]: "The element is not in the domain of the bilinear map.";
  
  A, B := Explode(dom);
  C := Codomain(f);
  
  hom_comps := {@ i : i in [1..#Subspaces(A)] | not IsZero(a`elt[i])@};
  require #hom_comps eq 1: "The element given must lie in the homogeneous component of the trivial module.";
  i := hom_comps[1];
  require IsIsomorphic(Irreducibles(A)[i], TrivialModule(Group(A), BaseRing(A))): "The element given must lie in the homogeneous component of the trivial module.";
  
  s := Vector(a`elt[i]);
  
  // f : R_k \otimes S_i \otimes T_j -> Z_k
  // Since U_i is the trivial module, R_k is 1-dimensional for every k.  Moreover, by Schur's lemma, we need only consider when j = k.
  // NB this requires U_j to be absolutely irreducible.
  
  require forall{U : U in Irreducibles(A) | Dimension(EndomorphismAlgebra(U)) eq 1} : "We require the irreducibles to be absolutely irreducible.";
  
  maps := [**];
  for j in [1..#Multiplicities(B)] do
    // Find the d = Dimension(S)*Dimension(R) = Dimension(S) matrices corresponding to the maps M in Hom(T \otimes Z, F^d)
    mats := AsMatrices(f`maps[i,j,j], 1, 0);
    
    hom_j := hom< Subspace(B, j) -> Subspace(C, j) | NumberOfRows(mat) eq 0 select [] else mat
             where mat := &+[ s[l]*mats[l] : l in [1..Degree(s)] | not IsZero(s[l]) ] >;
    Append(~maps, hom_j);
  end for;
  
  ad := New(GModDecHom);
  ad`domain := B;
  ad`codomain := C;
  ad`maps := maps;
  
  return ad;
end intrinsic;
