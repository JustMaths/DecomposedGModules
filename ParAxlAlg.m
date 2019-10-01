/*

We define a new class of object called a partial axial algebra, together with some functions for it to work.

*/

// Set this to the relative directory of where the library is
library_location := "../AxialAlgebras/library";

declare type ParAxlAlg[ParAxlAlgElt];

declare attributes ParAxlAlg:
  group,          // The automorphism group on the axes
  Miyamoto_group, // The Miyamoto group
  W,              // A vectorspace on which partial multiplication can be defined
  Wmod,           // A G-module representing the same vector space
  V,              // A vectorspace on which we know how to multiply
  mult,           // SeqEnum Multiplication table for V whose entries are ModTupFldElts
  GSet,           // The GSet of the axes
  tau,            // A map from the GSet to involutions in G
  shape,          // A SeqEnum of tuples < S, type> where S is a SetIndx of all axes in the
                  // subalgebra of shape type. We assume that the first two generate the subalgebra.
  GSet_to_axes,   // A map from the GSet to the elements of W which represent the axes
  number_of_axes, // The number of axes, which are always the last basis elements of W
  fusion_table,   // A FusTab which is the fusion table
  subalgs,        // A SubAlg
  axes,           // A SeqEnum of AxlAxis which are the axes
  rels;           // A SetIndx of relations which are elements of W

declare attributes ParAxlAlgElt:
  parent,         // parent
  elt;            // element

declare type SubAlg;

declare attributes SubAlg:
  subsps,         // A List of vector (sub)spaces
  maps,           // A List of tups < map, homg, j>, where map: subsps -> algs[j]`W is a hom
                  // and homg: Group(A) -> Group(alg) is a group hom
  algs;           // A SetIndx of partial algebras

declare type AxlAxis;

declare attributes AxlAxis:
  id,             // ParAxlAlgElt which is the idempotent
  stab,           // A GrpPerm which is the stabiliser of the axis
  inv,            // A GrpPermElt which is the Miyamoto involution in stab
  even,           // Assoc of sums of even eigenspaces
  odd;            // Assoc of odd eigenspace
/*

Programming note to self:

you can just coerce to move between vector spaces and G-modules

*/
declare verbose ParAxlAlg, 4;

intrinsic Hash(T::Tup) -> RngIntElt
  {
  }
  return &+[Hash(t) : t in T];
end intrinsic;

intrinsic Hash(T::List) -> RngIntElt
  {
  }
  return 1;
end intrinsic;
intrinsic 'eq'(A::Assoc, B::Assoc) -> BoolElt
  {
  Equality for AssociativeArrays.
  }
  return (Universe(A) cmpeq Universe(B)) and (Keys(A) eq Keys(B)) and forall{ k : k in Keys(A) | A[k] cmpeq B[k] };
end intrinsic;
//
//
// =============== PROPERTIES OF ParAxlAlgs =================
//
//
intrinsic Print(A::ParAxlAlg)
  {
  Prints a partial axial algebra.
  }
  num_axes := Join([ IntegerToString(#o) : o in Orbits(A`Miyamoto_group, A`GSet)], "+");
  if assigned A`axes then
    // The algebra should not be 0-dim
    if Dimension(A`W) eq Dimension(A`V) then
      printf "A %o-dimensional complete axial algebra for the group %o, %o axes, of shape %o", Dimension(A`W), GroupName(A`Miyamoto_group), num_axes, &cat [sh[2] : sh in A`shape];
    else
      printf "Partial axial algebra for the group %o, %o axes, of shape %o, dimension %o, with known multiplication of dimension %o", GroupName(A`Miyamoto_group), num_axes, &cat [sh[2] : sh in A`shape], Dimension(A`W), Dimension(A`V);
    end if;
  else
    assert Dimension(A`W) eq 0;
    printf "A 0-dimensional complete axial algebra for the group %o, %o axes, of shape %o", GroupName(A`Miyamoto_group), num_axes, &cat [sh[2] : sh in A`shape];
  end if;
end intrinsic;

intrinsic Shape(A::ParAxlAlg) -> Tup
  {
  Returns a short form of the shape of an algebra.
  }
  return < A`number_of_axes, &cat[ t[2] : t in A`shape]>;
end intrinsic;

intrinsic Dimension(A::ParAxlAlg) -> RngIntElt
  {
  Dimension of the partial algebra.
  }
  return Dimension(A`W);
end intrinsic;

intrinsic BaseField(A::ParAxlAlg) -> Rng
  {
  Base field of the partial algebra.
  }
  return BaseRing(A`W);
end intrinsic;

intrinsic BaseRing(A::ParAxlAlg) -> Rng
  {
  Base field of the partial algebra.
  }
  return BaseRing(A`W);
end intrinsic;

intrinsic Group(A::ParAxlAlg) -> GrpPerm
  {
  Group of the partial algebra.
  }
  return A`group;
end intrinsic;

intrinsic MiyamotoGroup(A::ParAxlAlg) -> GrpPerm
  {
  Miyamoto group of the partial algebra.
  }
  return A`Miyamoto_group;
end intrinsic;
/*
intrinsic Hash(A::ParAxlAlg) -> RngIntElt
  {
  }
  return Hash(A`W);  
end intrinsic;
*/
/*

============== Functions on ParAxlAlgs ===============

*/
/*

Changes the field for a partial axial algebra

*/
intrinsic ChangeField(A::ParAxlAlg, F::Fld) -> ParAxlAlg
  {
  Changes the field of definition of the partial axial algebra.  Checks that the eigenvalues do not collapse.
  
  Note that we need to be able to coerce any scalars into the new field.  For example, the rationals to a finite field is ok, but not the other way.
  }
  return ChangeRing(A, F);
end intrinsic;

function ChangeRingSeq(s, F, f);
  return [ ChangeRing(x, F, f) : x in s ];
end function;

intrinsic ChangeField(A::ParAxlAlg, F::Fld, f::Map) -> ParAxlAlg
  {
  Changes the field of definition of the partial axial algebra using the map f whose codomian is F.  Checks that the eigenvalues do not collapse.
  }
  require Codomain(f) eq F: 
    "The Codomain of the map given is not the chosen field";
  new_fusion_table := ChangeField(A`fusion_table, F, f);
  
  Anew := New(ParAxlAlg);
  Anew`Wmod := ChangeRing(A`Wmod, F, f);
  Wnew := ChangeRing(A`W, F, f);
  Anew`W := Wnew;
  // Doing ChangeRing sometimes changes the order of the basis elements.
  Anew`V := sub<Wnew | ChangeRingSeq(Basis(A`V), F, f) >;
  if assigned A`mult then
    Anew`mult := [ ChangeRingSeq(row, F, f) : row in A`mult ];
  end if;
  Anew`GSet := A`GSet;
  Anew`tau := A`tau;
  Anew`shape := A`shape;
  Anew`GSet_to_axes := map<Anew`GSet -> Anew`W | i:-> i@A`GSet_to_axes>;
  Anew`number_of_axes := A`number_of_axes;
  Anew`fusion_table := new_fusion_table;
  Anew`group := A`group;
  Anew`Miyamoto_group := A`Miyamoto_group;
  
  if assigned A`subalgs then
    subalgs := New(SubAlg);
    subalgs`subsps := [* sub<Wnew | ChangeRingSeq(Basis(U), F, f)> 
                    : U in A`subalgs`subsps *];
    subalgs`algs := {@ ChangeField(alg, F, f) : alg in A`subalgs`algs @};
    subalgs`maps := [* < 
       hom< subalgs`subsps[i] -> subalgs`algs[tup[3]]`W | 
           [ < subalgs`subsps[i].j, ChangeRing(A`subalgs`subsps[i].j@tup[1], F, f)> 
              : j in [1..Dimension(A`subalgs`subsps[i])]]>, 
         tup[2], tup[3] >
     where tup := A`subalgs`maps[i] : i in [1..#A`subalgs`maps] *];
   Anew`subalgs := subalgs;
  end if;
  
  if assigned A`axes then
    axes := [];
    for i in [1..#A`axes] do
      axis := New(AxlAxis);
      axis`id := Anew!ChangeRing(A`axes[i]`id`elt, F, f);
      axis`stab := A`axes[i]`stab;
      axis`inv := A`axes[i]`inv;
      axis`even := AssociativeArray();
      axis`odd := AssociativeArray();
      
      for attr in ["odd", "even"] do
        for key in Keys(A`axes[i]``attr) do
          axis``attr[key@f] := ChangeRing(A`axes[i]``attr[key], F, f);
        end for;
      end for;
      Append(~axes, axis);
    end for;
    Anew`axes := axes;
  end if;
  
  if assigned A`rels then
    Anew`rels := A`rels@f;
  end if;

  return Anew;
end intrinsic;

intrinsic ChangeRing(A::ParAxlAlg, F::Rng) -> ParAxlAlg
  {
  Changes the field of definition of the partial axial algebra.  Checks that the eigenvalues do not collapse.
  
  Note that we need to be able to coerce any scalars into the new field.  For example, the rationals to a finite field is ok, but not the other way.
  }
  new_fusion_table := ChangeRing(A`fusion_table, F);
  
  Anew := New(ParAxlAlg);
  Anew`Wmod := ChangeRing(A`Wmod, F);
  Wnew := RSpace(F, Degree(A`W));
  Anew`W := Wnew;
  // Doing ChangeRing sometimes changes the order of the basis elements.
  Anew`V := sub<Wnew | ChangeUniverse(Basis(A`V), Wnew)>;
  if assigned A`mult then
    Anew`mult := [ ChangeUniverse(row, Anew`W) : row in A`mult];
  end if;
  Anew`GSet := A`GSet;
  Anew`tau := A`tau;
  Anew`shape := A`shape;
  Anew`GSet_to_axes := map<Anew`GSet -> Anew`W | i:-> i@A`GSet_to_axes>;
  Anew`number_of_axes := A`number_of_axes;
  Anew`fusion_table := new_fusion_table;
  Anew`group := A`group;
  Anew`Miyamoto_group := A`Miyamoto_group;
  
  if assigned A`subalgs then
    subalgs := New(SubAlg);
    subalgs`subsps := [* sub<Wnew | ChangeUniverse(Basis(U), Wnew)> : U in A`subalgs`subsps *];
    subalgs`algs := {@ ChangeRing(alg, F) : alg in A`subalgs`algs @};
    subalgs`maps := [* < 
       hom< subalgs`subsps[i] -> subalgs`algs[tup[3]]`W | 
           [ < subalgs`subsps[i].j, ChangeRing(A`subalgs`subsps[i].j@tup[1], F)> : j in [1..Dimension(A`subalgs`subsps[i])]]>, 
         tup[2], tup[3] >
     where tup := A`subalgs`maps[i] : i in [1..#A`subalgs`maps] *];
   Anew`subalgs := subalgs;
  end if;
  
  if assigned A`axes then
    axes := [];
    for i in [1..#A`axes] do
      axis := New(AxlAxis);
      axis`id := Anew!ChangeRing(A`axes[i]`id`elt, F);
      axis`stab := A`axes[i]`stab;
      axis`inv := A`axes[i]`inv;
      axis`even := AssociativeArray();
      axis`odd := AssociativeArray();
      
      for attr in ["odd", "even"] do
        for key in Keys(A`axes[i]``attr) do
          axis``attr[ChangeUniverse(key, F)] := sub< Anew`W | [ Anew`W!Eltseq(u) : u in Basis(A`axes[i]``attr[key])]>;
        end for;
      end for;
      Append(~axes, axis);
    end for;
    Anew`axes := axes;
  end if;
  
  if assigned A`rels then
    Anew`rels := ChangeUniverse(A`rels, Wnew);
  end if;

  return Anew;
end intrinsic;

intrinsic RestrictToMiyamotoGroup(A::ParAxlAlg) -> ParAxlAlg
  {
  Return the algebra where the group is restricted to the Miyamoto group.
  }
  if A`Miyamoto_group eq A`group then
    return A;
  end if;
  
  Anew := New(ParAxlAlg);
  Miy := sub<Group(A) | Image(A`tau)>;
  ReduceGenerators(~Miy);
  Anew`group := Miy;
  Anew`Miyamoto_group := Miy;
  Anew`GSet := GSet(Miy, A`GSet);
  Anew`tau := map<Anew`GSet -> Miy | i:->i@A`tau>;
  Anew`shape := A`shape;
  Anew`number_of_axes := #Anew`GSet;
  Anew`fusion_table := A`fusion_table;
  
  Anew`Wmod := Restriction(A`Wmod, Miy);
  Anew`W := A`W;
  Anew`V := A`V;
  Anew`mult := A`mult;
  Anew`GSet_to_axes := map<Anew`GSet -> Anew`W | i :-> i@A`GSet_to_axes>;
  
  Anew`subalgs := A`subalgs;
  Anew`rels := A`rels;
  
  // We might have more axes classes than before
  orig_axes := {@ j : i in [1..#A`axes] | so where so := exists(j){j : j in A`GSet | j@A`GSet_to_axes eq A`axes[i]`id`elt} @};
  
  axis_classes := Sort({@ Representative(o) : o in Orbits(Miy, A`GSet) @});
  
  axes :=[];
  for ii in [1..#axis_classes] do
    i := axis_classes[ii];
    so := exists(t){<j, g> : j in orig_axes | so where so, g := IsConjugate(Group(A`GSet), A`GSet, j, i)};
    assert so;
    jj, g := Explode(t);
    j := Position(orig_axes, jj);
    
    idem := New(AxlAxis);
    idem`id := Anew!((A`axes[j]`id*g)`elt);
    assert i@Anew`GSet_to_axes eq idem`id`elt;
    idem`stab := A`axes[j]`stab^g meet Miy;
    idem`inv := A`axes[j]`inv^g;
    idem`odd := AssociativeArray();
    idem`even := AssociativeArray();
        
    if IsIdentity(g) then
      for gr in {"odd", "even"}, k in Keys(A`axes[j]``gr) do
        idem``gr[k] := A`axes[j]``gr[k];
      end for;
    else
      for gr in {"odd", "even"}, k in Keys(A`axes[j]``gr) do
        idem``gr[k] := sub<Anew`W | [Anew`W | ((A!v)*g)`elt : v in Basis(A`axes[j]``gr[k])]>;
      end for;
    end if;
      Append(~axes, idem);
  end for;
  Anew`axes := axes;
  
  return Anew;
end intrinsic;
/*

m-closed

*/
intrinsic mClosed(A::ParAxlAlg) -> RngIntElt
  {
  Returns the m for which the algebra is m-closed i.e. the algebra is spanned by products of the axes of length up to m.
  }
  require A`V eq A`W: "Can't calculate m-closed before calculating the algebra!.";
  if Dimension(A) eq 0 then
    return 0;
  end if;
  G := Group(A);
  W := A`W;
  axes := Setseq(Image(A`GSet_to_axes));

  U := sub<W | axes>;
  products := [axes];

  m := 1;
  while Dimension(U) ne Dimension(W) do
    m +:=1;
    // Multiplication is commutative, so we just need to do all pairs up to half the dimension
    UU := sub<W| Flat([ BulkMultiply(A, products[i], products[m-i]) : i in [1..Floor(m/2)]])>;
    Append(~products, Basis(UU));
    U +:= UU;
  end while;
  
  return m;
end intrinsic;
//
// ================ EQUALITY OF ParAxlAlgs ======================
//
intrinsic 'eq'(A::ParAxlAlg, B::ParAxlAlg) -> BoolElt
  {}
  attrs := GetAttributes(ParAxlAlg);
  if not forall{ attr : attr in attrs | assigned A``attr eq assigned B``attr} then
    return false;
  end if;
  for attr in attrs do
    if assigned A``attr and A``attr cmpne B``attr then
      return false;
    end if;
  end for;
  return true;
end intrinsic;

intrinsic IsEqual(U::ModGrp, V::ModGrp) -> BoolElt
  {}
  if Dimension(U) ne Dimension(V) or BaseRing(U) ne BaseRing(V) or Group(U) ne Group(V) then
    return false;
  end if;
  return ActionGenerators(U) eq ActionGenerators(V);  
end intrinsic;

intrinsic IsEqual(A::SubAlg, B::SubAlg) -> BoolElt
  {}
  attrs := Set(GetAttributes(SubAlg));
  if not forall{ attr : attr in attrs | assigned A``attr eq assigned B``attr} then
    return false;
  end if;
  if A`subsps ne B`subsps then
    return false;
  elif not forall{ i : i in [1..#A`maps] | A`maps[i,2] eq B`maps[i,2] and A`maps[i,3] eq B`maps[i,3]} then
    return false;
  elif not forall{ i : i in [1..#A`maps] | Domain(A`maps[i,1]) eq Domain(B`maps[i,1]) and Image(A`maps[i,1]) eq Image(B`maps[i,1]) and Basis(Domain(A`maps[i,1])) eq Basis(Domain(B`maps[i,1])) and [u@A`maps[i,1] : u in Basis(Domain(A`maps[i,1]))] eq [u@B`maps[i,1] : u in Basis(Domain(B`maps[i,1]))]} then
    return false;
  elif not forall{ i : i in [1..#A`algs] | IsEqual(A`algs[i], B`algs[i])} then
    return false;
  end if;
  return true;
end intrinsic;

intrinsic IsEqual(A::AxlAxis, B::AxlAxis) -> BoolElt
  {}
  attrs := Set(GetAttributes(AxlAxis));
  if not forall{ attr : attr in attrs | assigned A``attr eq assigned B``attr} then
    return false;
  end if;
  for attr in attrs diff {"id"} do
    if assigned A``attr and A``attr ne B``attr then
      return false;
    end if;
  end for;
  if assigned A`id and A`id`elt ne B`id`elt then
    return false;
  end if;
  return true;
end intrinsic;

intrinsic IsEqual(A::ParAxlAlg, B::ParAxlAlg) -> BoolElt
  {}
  attrs := Set(GetAttributes(ParAxlAlg));
  if not forall{ attr : attr in attrs | assigned A``attr eq assigned B``attr} then
    return false;
  end if;
  for attr in attrs diff {"Wmod", "subalgs", "axes", "tau", "GSet_to_axes"} do
    if assigned A``attr and A``attr ne B``attr then
      return false;
    end if;
  end for;
  
  // Now we need to check the other items
  so, iso := IsIsomorphic(A`Miyamoto_group, B`Miyamoto_group);
  if not so then
    return false;
  elif not IsEqual(A`Wmod, B`Wmod) then
    return false;
  elif assigned A`subalgs and not IsEqual(A`subalgs, B`subalgs) then
    return false;
  elif #A`axes ne #B`axes or not forall{ i : i in [1..#A`axes] | IsEqual(A`axes[i], B`axes[i])} then;
    return false;
  elif [ i@A`tau@iso : i in A`GSet] ne [i@B`tau : i in B`GSet] then
    return false;
  elif Image(A`GSet_to_axes) ne Image(B`GSet_to_axes) then
    return false;
  end if;
  return true;
end intrinsic;

intrinsic Basis(A::ParAxlAlg) -> SeqEnum
  {
  Basis of the partial algebra.
  }
  return [ CreateElement(A, v) : v in Basis(A`W)];
end intrinsic;

intrinsic '.'(A::ParAxlAlg, i::RngIntElt) -> ParAxlAlgElt
  {
  The ith basis element of the partial algebra.
  }
  bas := Basis(A);
  require i gt 0 and i le #bas: "Argument 2 (", i, ") should be in the range", [1..#bas];
  return Basis(A)[i];
end intrinsic;
//
//
// =========== PARTIAL AXIAL ALGEBRA ELEMENTS =============
//
//
intrinsic Parent(x::ParAxlAlgElt) -> ParAxlAlg
  {
  Parent of x.
  }
  return x`parent;
end intrinsic;

intrinsic Print(x::ParAxlAlgElt)
  {
  Print x.
  }
  printf "%o", x`elt;
end intrinsic;

intrinsic 'eq'(x::ParAxlAlgElt, y::ParAxlAlgElt) -> BoolElt
  {
  Equality of elements.
  }
  require x`parent eq y`parent: "The two elements are not in the same partial axial algebra.";
  return x`elt eq y`elt;
end intrinsic;

intrinsic 'in'(x::ParAxlAlgElt, A::ParAxlAlg) -> BoolElt
  {
  Returns whether x is in A.
  }
  return x`parent eq A;
end intrinsic;

intrinsic 'in'(x::ParAxlAlgElt, U::ModTupRng) -> BoolElt
  {
  Returns whether x is in the subspace U of the partial axial algebra.
  }
  require U subset Parent(x)`W: "U is not a subspace of the axial algebra containing x.";
  return x`elt in U;
end intrinsic;

// maybe this should be a function?
intrinsic CreateElement(A::ParAxlAlg, x::.) -> ParAxlAlgElt
  {
  Creates an element.
  }
  xx := New(ParAxlAlgElt);
  xx`parent := A;
  xx`elt := (A`W)!x;
  
  return xx;
end intrinsic;

intrinsic IsCoercible(A::ParAxlAlg, x::.) -> BoolElt, .
  {
  Returns whether x is coercible into A and the result if so.
  }
  W := A`W;
  if Type(x) eq ParAxlAlgElt and x`parent eq A then
    return true, x;
  end if;
  n := Degree(W);
  so := false;
  if (Type(x) eq SeqEnum and #x eq n) or ISA(Type(x), ModTupRngElt) then
    so := IsCoercible(W, x);
  elif Type(x) eq ModGrpElt then
    so := IsCoercible(A`Wmod, x);
  elif Type(x) eq RngIntElt and x eq 0 then
    return true, CreateElement(A, [0 : i in [1..Dimension(A)]]);
  end if;

  if not so then
    return false, "Illegal coercion.";
  else
    return true, CreateElement(A, Eltseq(x));
  end if;
end intrinsic;

intrinsic Hash(x::ParAxlAlgElt) -> RngIntElt
  {
  Returns the hash value of x.
  }
  return Hash(x`elt);
end intrinsic;

intrinsic Eltseq(x::ParAxlAlgElt) -> SeqEnum
  {
  Returns the sequence of coefficients of x`elt.
  }
  return Eltseq(x`elt);
end intrinsic;

intrinsic Vector(x::ParAxlAlgElt) -> ModTupFld
  {
  Returns the vector.
  }
  return x`elt;
end intrinsic;

intrinsic IsZero(x::ParAxlAlgElt) -> BoolElt
  {
  Returns whether an element is zero or not.
  }
  return IsZero(x`elt);
end intrinsic;
//
//
// ============ OPERATIONS FOR ELEMENTS ==============
//
//
intrinsic '+'(x::ParAxlAlgElt, y::ParAxlAlgElt) -> ParAxlAlgElt
  {
  Sums x and y.
  }
  require Parent(x) eq Parent(y): "x and y are not in the same partial axial algebra.";
  return CreateElement(Parent(x), x`elt+y`elt);
end intrinsic;

intrinsic '-'(x::ParAxlAlgElt) -> ParAxlAlgElt
  {
  Negation of the input.
  }
  return CreateElement(Parent(x), -x`elt);
end intrinsic;

intrinsic '-'(x::ParAxlAlgElt, y::ParAxlAlgElt) -> ParAxlAlgElt
  {
  Subtracts x and y.
  }
  require Parent(x) eq Parent(y): "x and y are not in the same partial axial algebra.";
  return CreateElement(Parent(x), x`elt-y`elt);
end intrinsic;

intrinsic '*'(al::RngElt, x::ParAxlAlgElt) -> ParAxlAlgElt
  {
  Returns the product of al and x.
  }
  require al in BaseRing(Parent(x)`W): "The scalar given is not in the base ring of the algebra.";
  return CreateElement(Parent(x), al*x`elt);
end intrinsic;

intrinsic '*'(x::ParAxlAlgElt, al::RngElt) -> ParAxlAlgElt
  {
  "
  }
  return al*x;
end intrinsic;

intrinsic '/'(x::ParAxlAlgElt, al::RngElt) -> ParAxlAlgElt
  {
  Returns x divided by al.
  }
  require al in BaseRing(Parent(x)`W): "The scalar given is not in the base ring of the algebra.";
  return CreateElement(Parent(x), (1/al)*x`elt);
end intrinsic;

intrinsic '*'(x::ParAxlAlgElt, y::ParAxlAlgElt) -> ParAxlAlgElt
  {
  Returns the product of x and y, if it exists.
  }
  require Parent(x) eq Parent(y): "x and y are not in the same partial axial algebra.";
  so, xy := IsTimesable(x, y);
  if so then
    return xy;
  else
    return false;
  end if;
end intrinsic;

intrinsic '*'(x::ParAxlAlgElt, g::GrpPermElt) -> ParAxlAlgElt
  {
  The image of x under the action of g.
  }
  A := Parent(x);
  require g in Group(A`Wmod): "g is not a member of the group which acts on the partial axial algebra which contains x.";
  return CreateElement(A, ((A`Wmod)!(x`elt))*g);
end intrinsic;
/*

============== intrinsics for subalgebras ==============

*/
intrinsic 'eq'(A::SubAlg, B::SubAlg) -> BoolElt
  {}
  for attr in GetAttributes(SubAlg) do
    if assigned A``attr then
      if not assigned B``attr or not(A``attr cmpeq B``attr) then
        return false;
      end if;
    elif assigned B``attr then
      if not assigned A``attr or not (A``attr cmpeq B``attr) then
        return false;
      end if;
    end if;
  end for;
  return true;
end intrinsic;
/*

================= intrinsics for axes =================

*/
intrinsic 'eq'(A::AxlAxis, B::AxlAxis) -> BoolElt
  {}
  for attr in GetAttributes(AxlAxis) do
    if assigned A``attr then
      if not assigned B``attr or not(A``attr cmpeq B``attr) then
        return false;
      end if;
    elif assigned B``attr then
      if not assigned A``attr or not (A``attr cmpeq B``attr) then
        return false;
      end if;
    end if;
  end for;
  return true;
end intrinsic;
/*

============== Dimensions of all the eigenspaces ===============

*/
intrinsic Subsets(S::SetIndx:empty := true) -> SetIndx
  {
  Returns the subsets of S orders by length and lexicographically wrt S
  }
  S_Sort := func<x,y | Position(S, x) - Position(S, y)>;
  function sub_Sort(x,y)
    if #x-#y ne 0 then
      return #x-#y;
    elif x eq y then
      return 0;
    else
      assert exists(i){i : i in [1..#x] | x[i] ne y[i]};
      return Position(S, x[i]) - Position(S, y[i]);
    end if;
  end function;
  
  subsets := Subsets(Set(S));
  if not empty then
    subsets diff:= {{}};
  end if;
  
  return Sort({@ Sort(IndexedSet(T), S_Sort) : T in subsets @}, sub_Sort);
end intrinsic;

intrinsic CheckEigenspaceDimensions(A::ParAxlAlg: U := A`W, empty := false) -> SeqEnum
  {
  Returns the dimensions of the eigenspaces for the idempotents.  Optional argument for intersecting all eigenspaces with U.
  }
  if not assigned A`axes then
    return [];
  end if;
  
  // find the even and off subspaces
  Ggr, gr := Grading(A`fusion_table); 
  require Order(Ggr) in {1,2}: "The fusion table is not Z_2-graded.";
  
  evens := {@ lambda : lambda in A`fusion_table`eigenvalues | lambda@gr eq Ggr!1 @};
  odds := {@ lambda : lambda in A`fusion_table`eigenvalues | lambda@gr eq Ggr.1 @};
  even_subs := Subsets(evens: empty := empty);
  odd_subs := Subsets(odds: empty:=false);
  
  return [ [ Dimension(U meet A`axes[i]`even[s]) : s in even_subs ] 
       cat [ Dimension(U meet A`axes[i]`odd[s]) : s in odd_subs ] 
         : i in [1..#A`axes]];
end intrinsic;
/*

=============== ALGEBRA MULTIPLICATION ==================

*/
/*

Calculates the multiplication in the partial algebra for elements of V.

NB u and v must be in A`V!!

*/
intrinsic Times(u::ParAxlAlgElt, v::ParAxlAlgElt) -> ParAxlAlgElt
  {
  For u and v in V, calculate the product u*v.
  }
  A := Parent(u);
  require A eq Parent(v): "Both elements do not lie in a common partial axial algebra.";
  V := A`V;
  require u in V and v in V: "Cannot multiply elements which are not in V.";
  uu := Coordinates(V, u`elt);
  vv := Coordinates(V, v`elt);
  // could even check to see if product is 0 but will run into trouble with summing over an empty seq
  dim := Dimension(V);
  return CreateElement(A, &+[ A`W | (uu[i]*vv[j] + uu[j]*vv[i])*A`mult[i,j] : i in [j+1..dim], j in [1..dim] | (uu[i] ne 0 and vv[j] ne 0) or (uu[j] ne 0 and vv[i] ne 0)] + &+[ A`W | uu[i]*vv[i]*A`mult[i,i] : i in [1..dim] | uu[i] ne 0 and vv[i] ne 0]);
end intrinsic;
/*

If (conjugates of) two elements of W both lie in a subalgebra in which we can multiply, then we can multiply them in the partial algebra.

*/
//  Coerces v into Wmod, applies g and coerces the result back into the parent vector space of v.
function Image(g, Wmod, v)
  return Parent(v)!((Wmod!v)*g);
end function;

intrinsic IsTimesable(u::ParAxlAlgElt, v::ParAxlAlgElt) -> BoolElt, ParAxlAlgElt
  {
  Tests whether u and v can be multiplied and if so returns their product.
  }
  A := Parent(u);
  require A eq Parent(v): "Both elements do not lie in a common partial axial algebra.";

  if assigned A`V and u`elt in A`V and v`elt in A`V then
    return true, Times(u, v);
  end if;

  W := A`W;
  Wmod := A`Wmod;
  G := Group(Wmod);

  i_subalgs := [ i : i in [1..#A`subalgs`subsps] | exists{ g : g in G | Image(g, Wmod, u`elt) in A`subalgs`subsps[i] and Image(g, Wmod, v`elt) in A`subalgs`subsps[i] }];

  if IsEmpty(i_subalgs) then
    return false, _;
  end if;

  for i in i_subalgs do
    subsp := A`subalgs`subsps[i];
    phi, _, j := Explode(A`subalgs`maps[i]);
    alg := A`subalgs`algs[j];

    gs := [ g : g in G | Image(g, Wmod, u`elt) in subsp and Image(g, Wmod, v`elt) in subsp ];
    for g in gs do
      uu:= Image(g, Wmod, u`elt) @ phi;
      vv:= Image(g, Wmod, v`elt) @ phi;
      so, uv := HasPreimage(Times(alg!uu,alg!vv)`elt, phi);
      if so then
        return true, CreateElement(A, Image(g^-1, Wmod, W!uv));
      end if;
    end for;
  end for;
  return false, _;
end intrinsic;
//
// ============= FUNCTIONS TO APPLY MAPS TO SETS OF ELMENTS ==============
//
/*

A handy function for applying a homomorphism to a set/sequence of vectors quickly.  I think it is quicker as magma uses fast matrix multiplication.

*/
intrinsic FastFunction(L::SeqEnum, map::Map:
   matrix := Matrix(BaseRing(Domain(map)), Dimension(Domain(map)), Dimension(Codomain(map)), [u@map : u in Basis(Domain(map))])) -> SeqEnum
  {
  Given a set or sequence of vectors and a homomorphism, returns the sequence which is the application of the map to each.  Uses matrix methods to achieve a speed up.
  }
  if #L eq 0 then
    return [];
  end if;
  require L[1] in Domain(map): "The elements of L must be in the domain of the map.";
  return [ Codomain(map) | v : v in Rows(Matrix(L)*matrix)];
end intrinsic;

intrinsic FastFunction(L::SetIndx, map::Map:
   matrix := Matrix(BaseRing(Domain(map)), Dimension(Domain(map)), Dimension(Codomain(map)), [u@map : u in Basis(Domain(map))])) -> SetIndx
  {
  Given a set or sequence of vectors and a homomorphism, returns the set which is the application of the map to each.  Uses matrix methods to achieve a speed up.
  }
  if #L eq 0 then
    return [];
  end if;
  require L[1] in Domain(map): "The elements of L must be in the domain of the map.";
  return {@ Codomain(map) | v : v in Rows(Matrix(Setseq(L))*matrix)@};
end intrinsic;

intrinsic FastMatrix(L::SeqEnum, matrix::Mtrx) -> SeqEnum
  {
  Given a set or sequence of vectors and a matrix, returns the sequence which is the application of the matrix to each.  Uses matrix methods to achieve a speed up.
  }
  if #L eq 0 then
    return [];
  end if;
  return [ v : v in Rows(Matrix(L)*matrix)];
end intrinsic;

intrinsic FastMatrix(L::SetIndx, matrix::Mtrx) -> SetIndx
  {
  Given a set or sequence of vectors and a homomorphism, returns the set which is the application of the matrix to each.  Uses matrix methods to achieve a speed up.
  }
  if #L eq 0 then
    return {@@};
  end if;
  return {@ v : v in Rows(Matrix(Setseq(L))*matrix)@};
end intrinsic;
/*

We now provide functions for fast multiplication of an element by a collection of elements or of two collections of elements together.  This uses the fast matrices above.

*/
intrinsic FastMultiply(L::SeqEnum, v::ParAxlAlgElt) -> SeqEnum
  {
  Given a sequence L of vectors, partial axial algebra elements, or sequences of coordinates in V, return the product of these with the partial axial algebra element v.
  }
  A := Parent(v);
  V := A`V;
  require v`elt in V: "The element given is not in V.";
  if #L eq 0 then
    return [];
  elif IsZero(v) then
    return [ A!0 : i in [1..#L]];
  end if;
  
  vv := Coordinates(V, v`elt);
  mat := &+[ Matrix( [vv[i]*A`mult[j,i] : j in [1..Dimension(V)]]) : i in [1..Dimension(V)] | vv[i] ne 0];
  
  require Type(L[1]) in {ParAxlAlgElt, ModTupFldElt, ModTupRngElt, SeqEnum}: "The list given is not in a partial alxial algebra.";
  if Type(L[1]) eq ParAxlAlgElt then
    L := [ l`elt : l in L];
    require forall{ l : l in L | l in V}: "The list of elements given are not in V.";
    L := [Coordinates(V, l) : l in L];
    return [ A!u : u in FastMatrix(L, mat)];
  elif ISA(Type(L[1]), ModTupRngElt) then
    require forall{ l : l in L | l in V}: "The list of elements given are not in V.";
    L := [Coordinates(V, l) : l in L];
  end if;
  
  return FastMatrix(L, mat);
end intrinsic;

intrinsic FastMultiply(A::ParAxlAlg, L::SeqEnum, v::ModTupRngElt) -> SeqEnum
  {
  Given a sequence L of vectors, partial axial algebra elements, or sequences of coordinates in V, return the product of these with the partial axial algebra element of A represented by v.
  }
  require IsCoercible(A,v): "The element given does not represent an element of A.";
  V := A`V;
  require v in V: "The element given is not in V.";
  if #L eq 0 then
    return [];
  elif IsZero(v) then
    return [ A`W!0 : i in [1..#L]];
  end if;

  vv := Coordinates(V, v);
  mat := &+[ Matrix( [vv[i]*A`mult[j,i] : j in [1..Dimension(V)]]) : i in [1..Dimension(V)] | vv[i] ne 0];

  require Type(L[1]) in {ParAxlAlgElt, ModTupFldElt, ModTupRngElt, SeqEnum}: "The list given is not in a partial alxial algebra.";
  if Type(L[1]) eq ParAxlAlgElt then
    L := [ l`elt : l in L];
    require forall{ l : l in L | l in V}: "The list of elements given are not in V.";
    L := [Coordinates(V, l) : l in L];
    return [ A!u : u in FastMatrix(L, mat)];
  elif ISA(Type(L[1]), ModTupRngElt) then
    require forall{ l : l in L | l in V}: "The list of elements given are not in V.";
    L := [Coordinates(V, l) : l in L];
  end if;
  
  return FastMatrix(L, mat);
end intrinsic;

intrinsic FastMultiply(A::ParAxlAlg, L::SeqEnum, v::SeqEnum) -> SeqEnum
  {
  Given a sequence L of vectors, partial axial algebra elements, or sequences of coordinates in V, return the product of these with the partial axial algebra element of A represented by v.
  }
  V := A`V;
  require #v eq Dimension(V): "The element given does not represent an element of A in V.";
  if #L eq 0 then
    return [];
  elif Set(v) eq {0} or #v eq 0 then
    return [ A`W!0 : i in [1..#L]];
  end if;

  mat := &+[ Matrix( [v[i]*A`mult[j,i] : j in [1..Dimension(V)]]) : i in [1..Dimension(V)] | v[i] ne 0];

  require Type(L[1]) in {ParAxlAlgElt, ModTupFldElt, ModTupRngElt, SeqEnum}: "The list given is not in a partial alxial algebra.";
  if Type(L[1]) eq ParAxlAlgElt then
    L := [ l`elt : l in L];
    require forall{ l : l in L | l in V}: "The list of elements given are not in V.";
    L := [Coordinates(V, l) : l in L];
    return [ A!u : u in FastMatrix(L, mat)];
  elif ISA(Type(L[1]), ModTupRngElt) then
    require forall{ l : l in L | l in V}: "The list of elements given are not in V.";
    L := [Coordinates(V, l) : l in L];
  end if;

  return FastMatrix(L, mat);
end intrinsic;
/*

Calculate the batches of multiplications quickly

*/
intrinsic BulkMultiply(A::ParAxlAlg, L::SeqEnum) -> SeqEnum
  {
  Calculate the multiplication in A of L with L.  Returns a single sequence of vectors representing one half of the multiplications L[1]*L[1], L[2]*L[1], L[2]*L[2], L[3]*L[1] etc.
  }
  V := A`V;
  if #L eq 0 then
    return [];
  elif Dimension(V) eq 0 then
    return [ A`W!0 : i in [1..(#L*(#L+1) div 2)]];
  end if;
  
  require Type(L[1]) in {ParAxlAlgElt, ModTupFldElt, ModTupRngElt, SeqEnum}: "The elements given do not represent elements of A.";
  if Type(L[1]) eq ParAxlAlgElt then
    require Universe(L) eq A and forall{ l : l in L | l`elt in V}: "The list of elements given are not in V.";
    L := [ Coordinates(V, l`elt) : l in L];
  elif ISA(Type(L[1]), ModTupRngElt) then
    require forall{ l : l in L | l in V}: "The list of elements given are not in V.";
    L := [Coordinates(V, l) : l in L];
  end if;

  return &cat [ FastMultiply(A, L[1..i], L[i]) : i in [1..#L]];
end intrinsic;

intrinsic BulkMultiply(A::ParAxlAlg, L::SeqEnum, M::SeqEnum) -> SeqEnum
  {
  Calculate the multiplication in A of all elements of L with M.  Returns a sequence of sequences of vectors representing L[1]*M, L[2]*M etc.
  }
  V := A`V;
  if #M eq 0 then
    return [];
  elif #L eq 0 then
    return [ [] : m in M];
  end if;
  
  require Type(L) eq Type(M): "The two lists have different types.";
  require Type(L[1]) in {ParAxlAlgElt, ModTupFldElt, ModTupRngElt, SeqEnum}: "The elements given do not represent elements of A.";
  if Type(L[1]) eq ParAxlAlgElt then
    require Universe(L) eq A and Universe(M) eq A and forall{ l : l in L | l`elt in V} and forall{ m : m in M | m`elt in V}: "The lists of elements given are not in V.";
    L := [ Coordinates(V, l`elt) : l in L];
    M := [ Coordinates(V, m`elt) : m in M];
  elif ISA(Type(L[1]), ModTupRngElt) then
    require forall{ l : l in L | l in V} and forall{ m : m in M | m in V}: "The lists of elements given are not in V.";
    L := [Coordinates(V, l) : l in L];
    M := [Coordinates(V, m) : m in M];
  end if;
  
  // We minimise the number of matrix operations.
  if #L le #M then
    return [ FastMultiply(A, M, L[i]) : i in [1..#L]];
  else
    mult := [ FastMultiply(A, L, M[i]) : i in [1..#M]];
    return [[ mult[j,i] : j in [1..#M]] : i in [1..#L]];
  end if;
end intrinsic;

intrinsic BulkMultiply(mult::SeqEnum, I1::SeqEnum, I2::SeqEnum) -> SeqEnum
  {
  Let mult be an nxk array with entries being m-dimensional vectors representing the multiplication of a n-dimensional by a k-dimensional space.  I1 and I2 are sequences of inputs in the n-dimensional and k-dimensional spaces respectively.
  }
  // Could speed this up even more by optimising the number of matrix multiplications to be done.  Either k+a, or n+b?
  // can we eliminate some tr?
  if #mult eq 0 or #I1 eq 0 then
    return [];
  elif #mult[1] eq 0 or #I2 eq 0 then
    return [ [] : i in I1];
  end if;
  I1 := Matrix(I1);
  I2 := Transpose(Matrix(I2));
  a := NumberOfRows(I1);
  n := NumberOfColumns(I1);
  k := NumberOfRows(I2);
  b := NumberOfColumns(I2);
  m := Degree(mult[1,1]);

  // View mult as a list of k nxm matrices  
  mats := [ Matrix([mult[i,j] : i in [1..n]]) : j in [1..k]];
  out := [ I1*M : M in mats];
  
  // Now we have k axm matrices, we reform them as a mxk matrices
  out := [ Transpose(Matrix([ out[j,i] : j in [1..k]])) : i in [1..a]];
  out := [ Transpose(M*I2) : M in out];
  
  // We have a bxm matrices, we reform these into a single axb array whose entries are m-dimensional vectors
  return [[ out[i,j] : j in [1..b] ] : i in [1..a]];
end intrinsic;

/*
intrinsic SubConstructor(A::ParAxlAlg, seq) -> ParAxlAlg
  {}
  axes := Image(A`GSet_to_axes);
  if #seq eq 0 then
    return sub<A`W|>;
  end if;
  if Type(seq[1]) eq ParAxlAlgElt then
    seq := [ a`elt : a in seq ];
  elif Type(seq[1]) eq SeqEnum then
    seq := ChangeUniverse(seq, A`W);
  end if;
  require ISA(Type(seq[1]), ModTupRng): "You have not given a collection of vectors which represent elements of an algebra.";
  
  
  
  S := {@ A| tup[i] : i in [2..#tup]@};
  Asub := New(ParAxlAlg);
  
  WH := Restriction(A`Wmod, H);
  Asub`Wmod := sub< WH | [ WH!(s`elt) : s in S]>;
  Asub`W := GInvariantSubspace(WH, S);
  return Asub;
end intrinsic;
*/
