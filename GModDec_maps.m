/*

Maps between GModDecs

*/
declare type GModDecHom;

declare attributes GModDecHom:
  domain,           // A GModDec giving the domain
  image,            // A GModDec giving the image
  maps;             // A List of vector space homomorphisms representing the maps

import "GModDec.m": CreateElement;
/*

======== Basic properties of maps ========

*/
intrinsic Print(f::GModDecHom)
  {
  Prints a GModDecHom.
  }
  printf "Homomorphism from: %o to %o", Domain(f), Image(f);
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
  M := f`domain;
  codims := [ Codomain(f`maps[i]) : i in [1..#f`maps]];
  return sub<M | codims>;
end intrinsic;

intrinsic Image(f::GModDecHom) -> GModDec
  {
  The image of the map f.
  }
  return f`image;
end intrinsic;

intrinsic Kernel(f::GModDecHom) -> GModDec
  {
  The kernel of the map f.
  }
  M := f`domain;
  kers := [ Kernel(f`maps[i]) : i in [1..#f`maps]];
  return sub<M | kers>;
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
function CreateMap(dom, im, maps)
  f := New(GModDecHom);
  f`domain := dom;
  f`image := im;
  f`maps := maps;
  return f;
end function;

// Really want to use the hom constructor here, but this isn't currently possible in magma
intrinsic DecomposedGModuleHomomorphism(M::GModDec, N::GModDec, S::[Map]) -> GModDecHom
  {
  Create a homomorphism between M and N given by a sequence of maps.
  }
  require BaseRing(M) eq BaseRing(N) and Group(M) eq Group(N): "The domain and image modules are not compatible.";
  require #S eq #M`irreducibles: "The number of maps given is not correct.";
  // require Type(S) in { List, SeqEnum, SetIndx} and #S eq #M`irreducibles and { Type(S[i]) : i in [1..#M`irreducibles] } subset { ModMatFldElt, ModMatRngElt, Map}: "The maps are not given in the required form.";
  
  // Can't just check if Domain(S[i]) eq M`subspaces[i] as this won't work for vectorspaces which aren't full ie are subspaces.
  // Might have got this working now.  Old check is BaseRing(Domain(S[i])) eq BaseRing(M) and Dimension(Domain(S[i])) eq Dimension(M`subspaces[i])
  require forall{ i : i in [1..#M`irreducibles] | Domain(S[i]) eq M`subspaces[i]}: "The domains of the given maps are not the homogeneous components of the given domain module.";
  // if fails, use same check as old check above.
  require forall{ i : i in [1..#N`irreducibles] | Image(S[i]) subset Generic(N`subspaces[i])}: "The images of the given maps are not contained in the homogeneous components of the given image module.";
  require forall{ i : i in [1..#N`irreducibles] | Codomain(S[i]) subset N`subspaces[i]}: "The codomain of the given maps are not contained in the homogeneous components of the given image module.";
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
  require f`image subset g`domain: "The domain of one map is not contained in the image of the other.";
  return CreateMap(f`domain, g`image, [ f`maps[i]*g`maps[i] : i in [1..#Domain(f)`irreducibles]]);
end intrinsic;

intrinsic Inverse(f::GModDecHom) -> GModDecHom
  {
  The inverse of f.
  }
  invs := [ Inverse(f`maps[i]) : i in [1..#f`maps]];
  return CreateMap(Codomain(f), f`domain, invs);
end intrinsic;
/*

======== Application of a map ========

*/
intrinsic '@'(m::GModDecElt, f::GModDecHom) -> GModDecElt
  {
  Apply f to m.
  }
  require m in f`domain: "The element is not in the domain of the map.";
  M := Generic(Parent(m));
  N := Generic(f`image);
  ff := [* Transpose(Matrix(BaseRing(M), M`multiplicities[i], N`multiplicities[i],
                  [ M`subspaces[i].j@f`maps[i] : j in [1..Dimension(M`subspaces[i])]]))
               : i in [1..#M`irreducibles] *];
  xx := [* ff[i]*m`elt[i] : i in [1..#f`maps] *];
  return CreateElement(Image(f), xx);
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
  return {@[ m@f : m in S@};
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
  require M`group eq f`domain`group and BaseRing(M) eq BaseRing(f`domain): "The module is not in the domain of the map.";

  Mnew := New(GModDec);
  Mnew`group := M`group;
  Mnew`irreducibles := M`irreducibles;
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;

  Mnew`subspaces := [ M`subspaces[i]@f`maps[i] : i in [1..#f`maps]];
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
  
  irredbas := < M`multiplicities[i] eq 0 select ZeroMatrix(F, 0,Dimension(M`irreducibles[i]))
                 else BasisMatrix(VectorSpace(M`irreducibles[i]))
                    : i in [1..#M`irreducibles]>;
  maps := < Dimension(Domain(f`maps[i])) eq 0 select ZeroMatrix(F, 0, Dimension(Codomain(f`maps[i])))
             else Dimension(Image(f`maps[i])) eq 0 select ZeroMatrix(F, Dimension(Domain(f`maps[i])), 0)
             else Matrix([v@f`maps[i] : v in Basis(Domain(f`maps[i]))])
                : i in [1..#f`maps] >;
  mat := DiagonalJoin(< TensorProduct(maps[i], irredbas[i]) : i in [1..#f`maps]>);
  return mat;
end intrinsic;
