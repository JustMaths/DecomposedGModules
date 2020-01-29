/*

========================== SHAPES =============================

*/
import "ParAxlAlg.m": library_location;
/*

A function for sorting the shapes

*/
ShapeSort := func<x,y | x[1] gt y[1] select -1 else x[1] lt y[1] select 1 else x[2] gt y[2] select 1 else x[2] lt y[2] select -1 else 0>;
/*

A function for sorting the tau maps, so we get a deterministic tau map

*/
function TauSort(f, g)
  X := Domain(f);
  for i in [1..#X] do
    imf := Eltseq(i@f);
    img := Eltseq(i@g);
    if imf lt img then
      return -1;
    elif imf gt img then
      return 1;
    end if;
  end for;
  return 0;
end function;
//
// ================= FINDING THE SHAPE ===================
//
/*

Given a permutation group, determines all the shapes of Axial algebras which are possible where we assume the axes are in bijection with a union of conjugacy classes

*/
intrinsic Shapes(G::GrpPerm) -> SeqEnum
  {
  Returns the shapes which coorespond to the action of G on a union of conjugacy classes of involutions.
  }
  all_shapes := [];
  Axs := InvolutionGSets(G);
  for Ax in Axs do
    taus := AdmissibleTauMaps(Ax);
    for tauset in taus do
      tau, stab := Explode(tauset);
      all_shapes cat:= Shapes(Ax, tau, stab);
    end for;
  end for;

  return all_shapes;
end intrinsic;

intrinsic ShapePrint(shapes)
  {
  Prints the shapes in a nice way.
  }
  require Type(shapes) in {List, SeqEnum} : "The given sequence does not describe shapes of an algebra";
  if #shapes ne 0 then
    require {#sh : sh in shapes} eq {3} and forall{sh : sh in shapes | Type(sh[2]) eq Map and ExtendedType(sh[3]) eq SeqEnum[Tup]}: "The given sequence does not describe shapes of an algebra";
  end if;
  print [ <GroupName(Group(sh[1])), [#o : o in Orbits(Group(sh[1]), sh[1])], &cat[t[2] : t in sh[3]]> : sh in shapes];
end intrinsic;
/*

Returns the GSets which are got in the old way.

*/
intrinsic InvolutionGSets(G::GrpPerm) -> SeqEnum
  {
  Returns a sequence of GSets which correspond to the action of G on a union of conjugacy classes of involutions.  We dedupe this for the action of the outer automorphism group of G.
  }
  class2 := {@ c[3] : c in Classes(G) | c[1] eq 2 @};

  orbs := {@ Orbit(G,x) : x in class2 @};
  // Two sets of involutions which are conjugate under an outer automorphism will produce the same posibilities for the shape.
 
  aut := AutomorphismGroup(G);
  autFP, FPmap := FPGroup(aut);
  out, out_map := OuterFPGroup(aut);
  outPerm, perm_map := PermutationGroup(out);

  elts_out := [ g@@perm_map@@out_map@FPmap : g in outPerm ];
  
  // We need to dedupe the set of all possible subsets of orbs for those which are conjugate under the outer automorphisms
  // At the same time, we check for generation of G
  
  all_invs := {@ @};
  for invs in {@ IndexedSet(x) : x in Subsets(Set(orbs)) | x ne {} @} do
    if sub<G | &join invs > ne G then
      continue;
    end if;
    if not exists(t){ f : f in elts_out | {@ GSet(G, o@f) : o in invs @} in all_invs } then
      Include(~all_invs, invs);
    end if;
  end for;

  all_GSets := [];
  for invs in all_invs do
    idems := &join invs;

    Ax := IndexedSet([1..#idems]);
    tau := map<Ax -> G | i :-> idems[i]>;
    AxxG := CartesianProduct(Ax, G);
    f := map< AxxG -> Ax | y :-> Position(idems,((y[1] @ tau)^y[2]))>;
    Ax := GSet(G, Ax, f);
    if IsTrivial(ActionKernel(G,Ax)) then
      Include(~all_GSets, Ax);
    end if;
  end for;
  
  return Sort(all_GSets, func< x,y| #x-#y>);
end intrinsic;
/*

Is a tau map admissible?  This may not be true when we restrict to a suborbit...

*/
intrinsic IsAdmissibleTauMap(Ax::GSet, tau::Map) -> BoolElt
  {
  returns whether a tau-map is admissible or not.
  }
  G := Group(Ax);
  if #Ax eq 1 then
    return 1@tau eq G!1;
  end if;
  require IsFaithful(G, Ax): "G does not act faithfully";
  orbs := Orbits(G, Ax);
  
  // We require tau to be a tau map
  if not sub<G| Image(tau)> eq G or
    not forall{ o : o in orbs | (o[1]@tau)^2 eq G!1 and o[1]@tau in Stabiliser(G, Ax, o[1])}
    or
    not forall{<i,g> : i in Ax, g in FewGenerators(G) | (i@tau)^g eq Image(g, Ax, i)@tau}
    then
    return false;
  end if;
  
  // Check if tau is admissible.
  // That is, for a pair a,b, |a^D| = |b^D| and other size properties
  pairs_orbs := Orbits(G, GSet(G,Ax,{ {@i,j@} : j in [i+1..#Ax], i in [1..#Ax]}));
  pairs_orb_reps := [ Representative(o) : o in pairs_orbs];
  
  for pair in pairs_orb_reps do
    D := sub<G | pair[1]@tau, pair[2]@tau>;
    o1 := Orbit(D, Ax, pair[1]);
    o2 := Orbit(D, Ax, pair[2]);
    if #o1 ne #o2 then
      return false;
    elif o1 eq o2 then
      if #o1 notin {3,5} then
        return false;
      end if;
    else
      if #o1 notin {1,2,3} then
        return false;
      end if;
    end if;
  end for;
  
  return true;
end intrinsic;
/*

Return the action on a set of tau maps

*/
intrinsic TauAction(Ax::GSet, tau_maps::SetIndx) -> GSet
  {
  Given a GSet Ax and a set of tau-maps on Ax, find the induced action on the tau maps.
  }
  G := Group(Ax);
  orbs := Orbits(G, Ax);
  phi, GG := Action(G, Ax);
  GAx := Stabiliser(Sym(#Ax), Set(orbs));
  N := Normaliser(GAx, GG);
  trans := Transversal(N, GG);
  // N is the automorphism group of the action of G on Ax
  
  // tau-maps are defined by their action on orbit representatives.
  orb_reps := [Representative(o) : o in orbs];
  
  // It's just as fast to form the function and then calculate the image of orb_reps as it is to only calculate the images of orb_reps (as tested on orb_rep of size 3)
  act := function(tau, n)
    return map<Ax-> G | i:-> ((((i^(n^-1))@tau)@phi)^n)@@phi >;
  end function;
  
  orb_images := {};
  all_tau_maps := [];
  
  // GG acts trivially on each tau, so we just need to check the transversal
  for t in tau_maps, n in trans do
    tau := act(t, n);
    Im_tau := orb_reps@tau;
    if not Im_tau in orb_images then
      Include(~orb_images, Im_tau);
      Append(~all_tau_maps, tau);
    end if;
  end for;
  
  all_tau_maps := IndexedSet(all_tau_maps);
  
  MapEq := function(f,g)
    return forall{i: i in orb_reps | i@f eq i@g};
  end function;
  
  tau_return := function(f)
    assert exists(g){g : g in all_tau_maps | MapEq(f,g)};
    return g;
  end function;

  tausxN := CartesianProduct(all_tau_maps, N);
  f := map< tausxN -> all_tau_maps | y :-> tau_return(act(y[1], y[2])) >;
  Taus := GSet(N, all_tau_maps, f);
  
  return Taus;
end intrinsic;
/*

Given a GSet Ax, returns the admissible tau maps together with their stabilisers.

*/
intrinsic AdmissibleTauMaps(Ax::GSet) -> SeqEnum
  {
  Given a GSet Ax, we find all the admissible tau maps up to automorphisms of the action.
  }
  G := Group(Ax);
  if #Ax eq 1 then
    return [map<Ax->G | i:->G!1>];
  end if;
  orbs := Orbits(G, Ax);

  orb_reps := [Representative(o) : o in orbs];
  possibles := [ #orbs[i] eq 1 select {@ Identity(G) @} 
        else {@ g : g in Centre(Stabiliser(G, Ax, orb_reps[i])) | Order(g) eq 2 @}
                   : i in [1..#orbs ]];
  
  cart := [ c : c in CartesianProduct(possibles)];
  
  tau_maps := {@ @};
  pairs_orbs := Orbits(G, GSet(G,Ax,{ {@i,j@} : j in [i+1..#Ax], i in [1..#Ax]}));
  pairs_orb_reps := [ Representative(o) : o in pairs_orbs];
  
  for poss in CartesianProduct(possibles) do
    def := &cat[ [ <j,poss[i]^g> where _,g := IsConjugate(G, Ax, orb_reps[i], j) : j in orbs[i]] : i in [1..#orbs]];
    Sort(~def, func<x,y|x[1]-y[1]>);
    def := [def[i,2] : i in [1..#def]];
    tau := map< Ax -> G | i:-> def[i]>;
  
    // We verify it is admissible
    for pair in pairs_orb_reps do
      D := sub<G | pair[1]@tau, pair[2]@tau>;
      o1 := Orbit(D, Ax, pair[1]);
      o2 := Orbit(D, Ax, pair[2]);
      if #o1 ne #o2 then
        continue poss;
      elif o1 eq o2 then
        if #o1 notin {3,5} then
          continue poss;
        end if;
      else
        if #o1 notin {1,2,3} then
          continue poss;
        end if;
      end if;
    end for;

    if sub<G | Image(tau)> ne G then
      continue poss;
    end if;
    
    Include(~tau_maps, tau);
  end for;
  
  if #tau_maps eq 0 then
    return [];
  end if;
  
  // We now wish to dedupe the set of tau maps using the automorphisms of Ax
  
  Taus := TauAction(Ax, tau_maps);
  N := Group(Taus);

  // We wish to get a deterministic algorithm, so we sort the tau-maps

  Taus_orbs := [ Sort(o, TauSort) : o in Orbits(N, Taus)];
  Taus_orb_reps := Sort([o[1] : o in Taus_orbs], TauSort);
  
  return [ <tau, Stabiliser(N, Taus, tau)> where tau := Taus_orb_reps[i]
              : i in [1..#Taus_orb_reps]];
end intrinsic;
/*

Given a GSet Ax and an admissible tau map, return the shapes of possible algebras, deduped by the action of stab.

*/
FindMinRep := function(orb, L, Ax)
  assert exists(l){ l : l in L | exists{ o : o in orb | o[1] eq l}};
  lorb := {@ x : x in orb | x[1] eq l @};
  assert exists(pair){ x : i in L cat [ i : i in Ax | i notin L] |
                     exists(x){x : x in lorb | x[2] eq i}};
  return pair;
end function;

intrinsic FindShapeConnectedComponents(Ax::GSet, tau::Map, axes::SetIndx: K := sub<Group(Ax) | [i@tau : i in axes]>) -> SeqEnum, SeqEnum
  {
  axes is a set of K-invariant axes, where the action is given by Ax and tau is an admissible tau-map.  We find the connected components of the graph on the dihedral subalgeras on axes.
  
  We return two sequences.  The elements of the second are sequences which represent the connected components.  Each connected component is a sequence of tuples < o, orbit>, where orbit is the orbit of o under K. The first is a sequence of representatives for the second.
  }
  require axes subset Ax: "The set of axes given is not a subset of the GSet.";
  require K subset sub<Group(Ax) | [i@tau : i in axes]>: "K must be a subgroup of the Miyamoto group.";
  require OrbitClosure(K, Ax, axes) eq axes: "The axes are not invariant under the group.";

  Sort(~axes);
  orbs := Orbits(K, GSet(K, Ax, axes));
  orb_reps := [o[1] : o in orbs];
  // We find the orbit representatives on pairs and so the possible 2-gen subalgebras
  pairs_orb_reps := [ FindMinRep(o, orb_reps, axes) : o in Orbits(ActionImage(K, GSet(K,Ax,{ {@i,j@} : i,j in axes | i ne j})))];
  
  // We assume throughout that the first two elements in the set generate the algebra.
  // NB by using a seq instead a set here for the list of subalgebras, we are allowing the same set of axes to define different dihedral subalgebras (although they must be of the same type).  eg, for 5A we do not assume that the extra basis element is the same for differnt pairs of generating axes.
  subalgs := [ &join{@ {@ Image(rho^k, Ax, o[1]), Image(rho^k, Ax, o[2] ) @} : k in [0..Order(rho)-1] @} where rho := (o[1]@tau)*(o[2]@tau): o in pairs_orb_reps ];
  Sort(~subalgs, func<x,y|#y-#x>); // Sort largest first
  
  // We do not get free choice over all the 2-gen subalgebras.  Some are contained in some others.
  // Formally, there is a graph with vertices being the subalgs and edges given by domination, where one subalgebra is contained in another.  We find the connected components.
  
  defining_shapes := [];
  for t in subalgs do
    involved := [ i : i in [1..#defining_shapes] | 
          exists{ sh : sh in defining_shapes[i] |
          exists{ j : j in [1..#sh[2]] |
               t subset sh[2,j] or sh[2,j] subset t }}];
    if #involved eq 0 then
      Append(~defining_shapes, [ < t, Orbit(K, Ax, t) > ]);
    else
      // We must merge all the shapes which are involved with the new one.
      defining_shapes[involved[1]] cat:= &cat [ defining_shapes[i] : i in involved[2..#involved] ] cat [ < t, Orbit(K, Ax, t) > ];
      for i in Reverse(involved)[1..#involved-1] do
        Remove(~defining_shapes, i);
      end for;
    end if;
  end for;

  defining_shape_reps := [ Sort([ t[1] : t in sets ], func<x,y|#y-#x>) : sets in defining_shapes ];
  
  return defining_shape_reps, defining_shapes;
end intrinsic;

intrinsic Shapes(Ax::GSet, tau::Map, stab::GrpPerm) -> SeqEnum
  {
  Given a GSet Ax and a tau map, we find all the possible shapes of algebra.
  }
  G := Group(Ax);
  Miy := sub<G | Image(tau)>;
  ReduceGenerators(~Miy);
  
  defining_shape_reps, defining_shapes := FindShapeConnectedComponents(Ax, tau, Ax: K := Miy);
  
  // Now we need to pick the possible choices for each connected component

  // If the subalgebra has 5, or 6 axes, there is no choice and it is 5A, or 6A
  shape := [];
  while #defining_shape_reps ne 0 and #defining_shape_reps[1,1] ge 5 do
    for o in defining_shape_reps[1] do
      // We must add each orbits which is in a connected component.
      // Those with a 6A, or 5A may only intersect others in 2A, or 3A.
      // Since any 2A, or 3A always appears as an intersection, we need not add these.
      // 2B and 3C cannot appear as intersections, and hence no 4As
      // But 4B can intersect in a 2A
      if #o eq 6 then 
        Append(~shape, < o, "6A" >);
      elif #o eq 5 then
        Append(~shape, < o, "5A" >);
      elif #o eq 4 then
        Append(~shape, < o, "4B" >);
      end if;
    end for;
    Remove(~defining_shape_reps, 1);
    Remove(~defining_shapes, 1);    
  end while;
    
  // Check whether there are any subalgebras left to define.
  if #defining_shape_reps eq 0 then
    return [ [*Ax, tau, shape*] ];
  end if;

  // There is choice over the remaining subalgebras: these are either length 2, 3, or 4
  // There are two choices for each

  // We wish to define an action of stab on the remaining defining_shapes
  
  def_shapes_orbs := [&join { t[2] : t in set} : set in defining_shapes];

  EltInOrb := function(x)
    assert exists(i){ i : i in [1..#def_shapes_orbs] | x in def_shapes_orbs[i]};
    return i;
  end function;

  num_shapes := IndexedSet([1..#defining_shapes]);
  numxstab := CartesianProduct(num_shapes, stab);
  stabact := map< numxstab -> num_shapes | y:-> EltInOrb(defining_shape_reps[y[1],1]^y[2])>;
  num_shapes := GSet(stab, num_shapes, stabact);

  H := ActionImage(stab, num_shapes);

  // We use this to act on our binary choices
  sortfn := function(x,y);
    if exists(i){i : i in [1..Degree(x)] | x[i] ne y[i]} then
      if x[i] eq 0 then
        return -1;
      else
        return 1;
      end if;
    end if;
    return 0;
  end function;
  
  binary_choices := Sort({@ v : v in VectorSpace(GF(2), #defining_shapes) @}, sortfn);
  bin_reps := Sort([ o[1] : o in Orbits(H, GSet(H, binary_choices))], sortfn);

  shapes := [];
  for b in bin_reps do
    // We now calculate the extra shapes
    // Note that since there are no orbits of length 5, or 6 left, the only intersections that may occur are 4s with 2s.
    // We need only count the 4s
    extra := &cat[ [ < defining_shape_reps[i,j], IntegerToString(#defining_shape_reps[i,j]) cat (b[i] eq 0 select "A" else "B") > : j in [1..#defining_shape_reps[i]] | #defining_shape_reps[i,j] eq #defining_shape_reps[i,1] ] : i in [1..Degree(b)]];
    // correct for 3B to 3C
    extra := [ x[2] eq "3B" select < x[1], "3C" > else x : x in extra];
    Append(~shapes, [*Ax, tau, shape cat extra *]);
  end for;

  return shapes;
end intrinsic;
/*

Checks isomorphism of shapes.

NB this will automatically restrict to an automorphism of the Miyamoto groups.

*/
intrinsic IsIsomorphic(Ax1::GSet, tau1::Map, shape1::SeqEnum, Ax2::GSet, tau2::Map, shape2::SeqEnum) -> BoolElt, GrpPermElt, Map
  {
  Tests if the shape defined by Ax1, tau1, and shape1 is isomorphic to the one defined by Ax2, tau2, shape2.  If so, it returns a pair, perm in Sym(|Ax1|) and homg:Miy1->Miy2 such that
  
  (i^g)^perm = (i^perm)^(g@homg) for all g in G1.
  
  i:->  i^(perm)^-1 @tau2^perm = tau2
  
  and perm maps shape1 to shape2.
  }
  if #Ax1 ne #Ax2 or {*sh[2] : sh in shape1*} ne {*sh[2] : sh in shape2*} then
    return false, _, _;
  end if;
  
  // Find the equivalence between the GSets
  Miy1 := sub<Group(Ax1) | Image(tau1)>;
  Miy2 := sub<Group(Ax2) | Image(tau2)>;
  act1, GG1 := Action(Miy1, Ax1);
  act2, GG2 := Action(Miy2, Ax2);
  so, perm := IsConjugate(Sym(#Ax1), GG1, GG2);
  if not so then
    return false, _, _;
  end if;
  homg := hom<Miy1 -> Miy2 | [<g,((g@act1)^perm)@@act2> : g in Generators(Miy1) join {Miy1!1}]>;
  assert2 forall{<i,g> : i in Ax1, g in Generators(Miy1) | Image(g,Ax1,i)^perm eq Image(g@homg, Ax2, i^perm)};
  
  // We form the tau map for the conjugated Ax1
  tau_adj := map<Ax2 -> Group(Ax2) | i:->(i^(perm^-1))@tau1@homg>;
  
  // Find the equivalence between the tau maps
  GAx2 := Stabiliser(Sym(#Ax2), Set(Orbits(Miy2, Ax2)));
  N := Normaliser(GAx2, GG2);

  // We must define equality of maps
  orb_reps := {@ o[1] : o in Orbits(Miy2, Ax2)@};
  MapEq := function(f,g)
    return forall{i: i in orb_reps | i@f eq i@g};
  end function;
    
  // The action on tau maps is
  // tau_n := tau(i^(n^-1))^n
  
  so := exists(n){n : n in N | MapEq(tau2, map<Ax2 -> Group(Ax2) |
                        i:-> (((i^(n^-1))@tau_adj@act2)^n)@@act2>)};
  
  if not so then
    return false, _, _;
  end if;
  
  perm := perm*n;
  homg := hom<Miy1 -> Miy2 | [<g,((g@act1)^perm)@@act2> : g in Generators(Miy1) join {Miy1!1}]>;
  assert2 MapEq(tau2, map<Ax2 -> Group(Ax2) | i:->(i^(perm^-1))@tau1@homg>);
  
  // Now we check to see if the shapes are the same
  
  // we can act with all the stabiliser of the tau-map
  stab := sub<N |{m : m in N | MapEq(tau2, map<Ax2 -> Group(Ax2) |
                        i:-> (((i^(m^-1))@tau2@act2)^m)@@act2>)}>;
  shape_orbs2 := [ Orbit(Miy2, Ax2, sh[1]) : sh in shape2 ];
  
  orbmember := function(S);
    assert exists(i){i : i in [1..#shape_orbs2] | S in shape_orbs2[i]};
    return i;
  end function;
  
  so := exists(h){h : h in stab | forall{sh : sh in shape1 | sh[2] eq shape2[orbmember(sh[1]^(perm*h)), 2] }};
  if not so then
    return false, _, _;
  end if;
  
  perm := perm*h;
  homg := hom<Miy1 -> Miy2 | [<g,((g@act1)^perm)@@act2> : g in Generators(Miy1) join {Miy1!1}]>;
  assert2 MapEq(tau2, map<Ax2 -> Group(Ax2) | i:->(i^(perm^-1))@tau1@homg>);
    
  return true, perm, homg;
end intrinsic;
/*

Find the stabiliser of a shape

*/
intrinsic ShapeStabiliserAction(Ax::GSet, tau::Map, shape::SeqEnum) -> GSet, Map
  {
  Find the stabiliser of the shape.
  }
  G := Group(Ax);
  phi, GG := Action(G, Ax);
  Taus := TauAction(Ax, {@ tau @});
  N := Group(Taus);

  if N eq GG then
    return Ax, hom<G->G | GeneratorsSequence(G)>;
  end if;
  
  Axnew := GSet(N);
  
  // We find the orbits of the shapes and group them by type
  types := {@ sh[2] : sh in shape @};
  
  shape_orbs := [ &join[ Orbit(G, Ax, sh[1]) : sh in shape | sh[2] eq type ]: type in types];
  
  // For some reason we can't just take stabilisers of orbits of pairs, or triples etc.
  // We must define a new GSet
  
  num_orbs := [ &join[ Orbit(G, Ax, sh[1]) : sh in shape | StringToInteger(sh[2,1]) eq i ]: i in [2..6]];
  
  numAx := AssociativeArray([* <i+1, GSet(N, Axnew, num_orbs[i])> : i in [1..5] | not IsEmpty(num_orbs[i])*]);
  
  stab := N;
  for sh in shape_orbs do
    stab := Stabiliser(stab, numAx[#sh[1]], sh);
  end for;
  
  return GSet(stab, Axnew), phi;
end intrinsic;
/*

Function to return the restriction of the shape to the set of axes given by axes

*/
intrinsic RestrictShape(Ax::GSet, tau::Map, shape::SeqEnum, axes::SetIndx : K := sub<Group(Ax) | [i@tau : i in axes]>) -> SeqEnum, SeqEnum
  {
  Given a shape type defined by Ax, tau and shape, and a set of axes acted upon by K, calculate the restriction of the shape to the set of axes.  Returns the type and the sequence of types seen from the original shape.
  }
  G := Group(Ax);
  require K subset sub<Group(Ax) | [i@tau : i in axes]>: "K must be a subgroup of the Miyamoto group.";
  
  full_type := [];  // records the full shape information
  type_flag := [ false : sh in shape];  // records the index of which types were seen

  Sort(~axes);
  
  defining_shape_reps := FindShapeConnectedComponents(Ax, tau, axes: K := K);
  // We must identify the shape in the larger algebra for each connected component.  The components from the larger algebra may split, but they cannot join.
  
  for rep in defining_shape_reps do
    for o in rep do
      // We need to record the subalgebras in a rep which are not contained in another.  These are all 6s, 5s and 4s.
      // If the size of the largest subalgebra is 6, we need to record 4s and 6s.
      // Otherwise, we just need to record the ones with size equal to the largest.
      // in all cases this means recording all 4s, 5s, and 6s or the first in the rep (if it is a 2, or 3 then it is either the only one in the rep, or is contained in something larger).
      // Since components from the larger algebra may split but not join, a defining subalgebra in the larger algebra must either be defining in the smaller algebra, or not intersect at all.  So when identifying which subalgebras from the larger algebra are seen in the smaller, we need only consider the defining subalgebras of the smaller algebra.
      
      if not (#o ge 4 or #o eq #rep[1]) then
        continue rep;
      end if;
      
      // check if we have the full image of a shape from Ax
      if exists(i){ i : i in [1..#shape], g in G | Image(g, Ax, shape[i,1]) eq o} then
        Append(~full_type, < o, shape[i,2]>);
        type_flag[i] := true;
        continue o;
      end if;
      
      // otherwise we must have an intersection of a 6A, or a 4A, 4B with axes
      assert #o in {2,3};
      // if subalg has size 3 it can only have come from a 6A
      if #o eq 3 then
        Append(~full_type, < o, "3A">);
        continue o;
      end if;
      
      assert exists(sh){ sh : sh in shape, g in G | Image(g, Ax, o) subset sh[1]};
      assert sh[2][1] in {"4", "6"};
      if sh[2] eq "4A" then
        Append(~full_type, < o, "2B">);
      else
        // sh is 4B, or 6A
        Append(~full_type, < o, "2A">);
      end if;
    end for;
  end for;
  Sort(~full_type, func<x,y | ShapeSort(x[2],y[2])>);
  
  return full_type, type_flag;
end intrinsic;
/*

Find all the helpful subalgebras we could glue in by checking subgroups.  Has a switch so to check if we have computed them and if so returns the gluing information.

*/
intrinsic GluingSubalgebras(L::List: subgroups := "maximal", field := Rationals(), FT := MonsterFusionTable(), gluing := false, partial := false) -> List, SeqEnum
  {
  This routine expects a List [* Ax, tau, shape *] and has two functions:

  If gluing = false (default), then given a field and the information for a axial algebra, it returns which subalgebras would be used to glue in.
  
  If gluing = true, then it returns a list of tuples <filename, map, homg> for subalgebras which have already been computed.  Here, if axes are the set of axes in Ax for a subalgebra, whose generated by the tau map is K, then map is a map from axes to the axes of the subalgebra and homg is an isomorphism from K to Group(subalgebra).
  
  The function also returns a set of flags showing which shapes have been covered by the subalgebras.
  
  Optional parameters:
    subgroups - "maximal" (default) uses the maximal subgroups, "all" uses all subgroups, or user can give a sequence of subgroups.
    partial - whether we consider partial algebras.
    FT - fusion table.
  }
  require #L eq 3 and Type(L[2]) eq Map and Type(L[3]) eq SeqEnum: "The input is not of the required form";

  return GluingSubalgebras(L[1], L[2], L[3]:
            subgroups := subgroups, field := field, FT := FT, gluing := gluing, partial := partial);
end intrinsic;

intrinsic GluingSubalgebras(Ax::GSet, tau::Map, shape::SeqEnum: subgroups := "maximal", field := Rationals(), FT := MonsterFusionTable(), gluing := false, partial := false) -> List, SeqEnum
  {
  This routine has two functions:

  If gluing = false (default), then given a field and the information for a axial algebra, it returns which subalgebras would be used to glue in.
  
  If gluing = true, then it returns a list of tuples <filename, map, homg> for subalgebras which have already been computed.  Here, if axes are the set of axes in Ax for a subalgebra, whose generated by the tau map is K, then map is a map from axes to the axes of the subalgebra and homg is an isomorphism from K to Group(subalgebra).
  
  The function also returns a set of flags showing which shapes have been covered by the subalgebras.
  
  Optional parameters:
    subgroups - "maximal" (default) uses the maximal subgroups, "all" uses all subgroups, or user can give a sequence of subgroups.
    partial - whether we consider partial algebras.
    FT - fusion table.
  }
  Miy := sub<Group(Ax)| Image(tau)>;
  
  // Build the list of subgroups to check
  if Type(subgroups) eq MonStgElt then
    require subgroups in {"all", "maximal"}: "subgroups must be \"all\", \"maximal\", or a sequence of subgroups";
    if subgroups eq "all" then
      subgroups := Reverse([ H`subgroup : H in Subgroups(Miy)]);
    else
      subgroups := [Miy] cat [ rec`subgroup : rec in MaximalSubgroups(Miy)];
    end if;
  else
    require ExtendedType(subgroups) eq SeqEnum[GrpPerm]: "subgroups must be \"all\", \"maximal\", or a sequence of subgroups";
    require forall{ H : H in subgroups | H subset Miy}: "The subgroups given are not contained in the Miyamoto group.";

    // Ensure the subgroups to search through are in the right order
    Sort(~subgroups, func<x,y|Order(y)-Order(x)>);
  end if;
  
  subalgs := [* *]; // our subalgs to return
  to_glue := {@ @}; // set of axes to have a subalgebra glued into.
  
  // Given a sequence <glued> of axes we have already glued an subalgebra onto, orbits <orbs> of some group we are considering and possible sets <subsets> of indices of these, amend <subsets> to remove the sets of indices which give axes which are contained in a set in <glued>.
  procedure RemoveSubsets(~subsets, orbs, glued)
    overalgs := { { i : i in [1..#orbs] | orbs[i] subset X } : X in glued};
    subsets := [ S : S in subsets | not exists{T : T in overalgs | S subset T} ];
  end procedure;

  // Procedure to add <subalg> on <axes> to the list <subalgs>, checking if <axes> are contained in, or contain a set of axes from glued
  procedure AddSubalg(~subalgs, ~glued, subalg, axes)
    is_subset := {@ i : i in [1..#glued] | axes subset glued[i] @};
    is_overset := {@ i : i in [1..#glued] | glued[i] subset axes @};
    
    if #is_overset ne 0 then
      subalgs := [* subalgs[i] : i in [1..#subalgs] | i notin is_overset *] cat [* subalg *];
      glued := {@ glued[i] : i in [1..#glued] | i notin is_overset @} join {@ axes @};
    elif #is_subset eq 0 then
      Append(~subalgs, subalg);
      Include(~glued, axes);
    end if;
  end procedure;
  
  shape_flags := [ false : sh in shape ];
  
  for H in subgroups do
    orbs := [ o : o in Orbits(H, Ax) | sub<Miy | o@tau> subset H];
    subsets := [ S : S in Subsets({1..#orbs}) | S ne {}];
    RemoveSubsets(~subsets, orbs, to_glue);
    Sort(~subsets, func<x,y|#y-#x>);
    if H eq Miy then
      Remove(~subsets, 1);
    end if;
        
    // We loop over all subsets.
    // if gluing = false, then just consider the maximal subset and return what the group and shape is for that
    // if gluing = true, then check to see whether it has been computed and if not descend to find computed algebras to glue in.  Dedupe by containment.
    
    while #subsets ne 0 do
      set := subsets[1];
      axes := &join orbs[Setseq(set)];
      Sort(~axes);
      K := sub<Miy | FewGenerators(sub<Miy | axes@tau>)>;
      
      num := IndexedSet([1..#axes]);
      numxK := CartesianProduct(num, K);
      f := map<numxK -> num | y:-> Position(axes, Image(y[2], Ax, axes[y[1]]))>;
      Kx := GSet(K, num, f);
      
      // Find a faithful action of a subgroup, K is a central extension of this.
      phi, K_faithful := Action(K, Kx);
      Kx_faithful := GSet(K_faithful, Kx);
      if IsTrivial(K_faithful) then
        Remove(~subsets, 1);
        continue;
      end if;
      
      Ktau := map<Kx -> K | i:-> axes[i]@tau>;
      Ktau_faithful := Ktau*phi;
      // I don't think this can happen!!
      if not IsAdmissibleTauMap(Kx_faithful, Ktau_faithful) then
        print "tau not addmissible.";
        Remove(~subsets, 1);
        continue;
      end if;
      
      if not gluing then
        // We find the GSet, tau and shape for the maximal elements
        Kshape, flags := RestrictShape(Ax, tau, shape, axes: K := K);
        Kshape := [ <{@ Position(axes, i) : i in t[1] @}, t[2]> : t in Kshape ];

        AddSubalg(~subalgs, ~to_glue, [*Kx_faithful, Ktau_faithful, Kshape*], axes);
        RemoveSubsets(~subsets, orbs, {@ axes @});
        Or(~shape_flags, flags);
        continue;
      else
        // We wish to search for any subalgebras and check whether we have completed them
        num_axes := Join([IntegerToString(#o) : o in Orbits(K_faithful, Kx_faithful)], "+");
        
        path := Sprintf("%o/%o/%m/%o/%o", library_location, FT`directory, field, MyGroupName(K_faithful), num_axes);
        if not ExistsPath(path) then
          Remove(~subsets, 1);
          continue;
        end if;
        algs := ls(path);
        
        // We remove partial algebras from the list
        if not partial then
          algs := [ alg : alg in algs | "partial" notin alg];
        end if;
        
        // We search for possible isomorphic algebras by checking the shape
        Kshape, flags := RestrictShape(Ax, tau, shape, axes: K := K);
        Kshape := [ <{@ Position(axes, i) : i in t[1] @}, t[2]> : t in Kshape ];
        
        alg_shapes := [ ParseShape(sh) : sh in algs];
        shape_type := ParseShape(&cat[t[2] : t in Kshape]);
        possibles := {@ i : i in [1..#alg_shapes] | alg_shapes[i] eq shape_type @};
        
        if #possibles eq 0 then
          Remove(~subsets, 1);
          continue;
        end if;
        
        // Have to do it this slightly awkward way so the continue statement works...
        so := false;
        index := 1;
        while not so and index le #possibles do
          j := possibles[index];
          alg_type := GetTypePartialAxialAlgebra(Sprintf("%o/%o", path, algs[j]));
          _, alg_ax, alg_tau, alg_shape, dim := Explode(alg_type);
          
          so, perm, homg := IsIsomorphic(Kx_faithful, Ktau_faithful, Kshape, alg_ax, alg_tau, alg_shape);
          index +:= 1;
        end while;
        
        // There is no match
        if not so then
          Remove(~subsets, 1);
          continue;
        end if;
        
        // We have found a match
        map := map< axes -> alg_ax | i :-> Position(axes, i)^perm>;
        
        // If the dimension is zero, it collapses the algebra and we return just this
        if dim eq 0 then
          vprintf ParAxlAlg, 4: "Found a 0-dim algebra to glue in on the axes %o with group %o.\n", axes, GroupName(K_faithful);
          return [*<Sprintf("%o/%o", path, algs[j]), map, phi*homg>*], shape_flags;
        end if;
        
        AddSubalg(~subalgs, ~to_glue, <Sprintf("%o/%o", path, algs[j]), map, phi*homg>, axes);
        RemoveSubsets(~subsets, orbs, {@ axes @});
        Or(~shape_flags, flags);
      end if;
    end while;
  end for;

  return subalgs, shape_flags;
end intrinsic;
