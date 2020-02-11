/*

Functions for creating an initial object

*/
import "ParAxlAlg.m": library_location;

QQ := Rationals();
/*

function for sorting eigenvalues in the order 1, 0, everything else

*/
function EigenvalueSort(x,y)
  if x eq 1 then
    return -1;
  elif y eq 1 then
    return 1;
  elif x eq 0 then
    return -1;
  elif y eq 0 then
    return 1;
  else
    return x-y;
  end if;
end function;
//
// ================ BUILD A PARTIAL AXIAL ALGEBRA =================
//
/*

We define an initial object

*/
intrinsic PartialAxialAlgebra(L::List: fusion_table := MonsterFusionTable(), field := QQ, subgroups := "maximal", partial := false, shape_stabiliser := true) -> ParAxlAlg
  {
  Given an L = [Ax, tau, shape] containing a GSet Ax for a group G, a map tau: Ax -> involutions of G and a shape for the algebra, we define an initial object.  shape should be given as a sequence of tuples <o, type>, where the axes o[1] and o[2] generate a subalgebra of the given type with axes o.
  }
  require Type(L[1]) eq GSetIndx and Type(L[2]) eq Map and Type(L[3]) eq SeqEnum: "The list of parameters is not in the required form.";
  return PartialAxialAlgebra(L[1],L[2],L[3]: fusion_table := fusion_table, field := field, subgroups := subgroups, partial := partial, shape_stabiliser := shape_stabiliser);
end intrinsic;
/*

Build an initial partial algebra

*/
intrinsic PartialAxialAlgebra(Ax::GSetIndx, tau::Map, shape::SeqEnum: fusion_table := MonsterFusionTable(), field := QQ, subgroups := "maximal", partial := false, shape_stabiliser := true) -> ParAxlAlg
  {
  Given a GSet Ax for a group G, a map tau: Ax -> involutions of G and a shape for the partial algebra, we define an initial object.  shape should be given as a sequence of tuples <o, type>, where the axes o[1] and o[2] generate a subalgebra of the given type with axes o.
  
  Optional arguments:
  fusion_table is a FusTab and defaults to the Monster fusion table.
  subgroups toggles which subalgebras to glue in.  If "maximal" (default) then it checks for subalgebra coming from maximal subgroups, if "all" if check for subalgebras coming from all subgroups, if "none" it just uses the subalgebras in the shape, or the user can specify a sequence of subgroups of the Miyamoto group.
  field defaults to the rationals.
  shape_stabiliser is a Boolean and if true extends the action to the stabiliser of the shape.
  }
  require Type(fusion_table) eq FusTab: "The fusion table given is not in the required form.";
  require IsField(field): "The field given is not a field!";
    
  A := New(ParAxlAlg);
  
  if shape_stabiliser then
    Ax, phi := ShapeStabiliserAction(Ax, tau, shape);
    tau := tau*phi;
    if ExtendedType(subgroups) eq SeqEnum[GrpPerm] then
      subgroups := subgroups@phi;
    end if;
  end if;
    
  A`GSet := Ax;
  A`tau := tau;
  A`shape := shape;
  A`number_of_axes := #Ax;
  if IsFinite(field) then
    fusion_table := ChangeField(fusion_table, field);
  end if;
  A`fusion_table := fusion_table;
  G := Group(Ax);
  A`group := G;
  Miy := sub<G | Image(tau)>;
  ReduceGenerators(~Miy);
  A`Miyamoto_group := Miy;

  Wmod, A`W_to_Wmod := DecomposedGModule(PermutationModule(G, Action(G, Ax), field));
  A`W := RSpace(field, Dimension(Wmod));
  A`Wmod := Wmod;
  W := A`W;
  A`GSet_to_axes := map<Ax -> W | i :-> W.i>;

  subalgs := New(SubAlg);
  subalgs`subsps := [* *];
  subalgs`algs := {@ @};
  subalgs`maps := [* *];

  // We set up flags for when we have glued in a subalgebra which uses the full basic algebra of that shape.

  shape_flags := [ false : sh in shape ];
  
  // We search for the subalgebras we have computed and glue them in.

  if not (Type(subgroups) eq MonStgElt and subgroups eq "none") then
    gluingsubalgs, flags := GluingSubalgebras(Ax, tau, shape: subgroups := subgroups, FT := fusion_table, field := field, gluing := true, partial := partial);
    
    for tup in gluingsubalgs do
      file, glue, homg := Explode(tup);
      alg := LoadPartialAxialAlgebra(file);

      // We could be trying to glue in an algebra which has collapsed
      // If so, ours also collapses
      if Dimension(alg) eq 0 then
        A`Wmod := GModule(G, MatrixAlgebra<field,0|[ZeroMatrix(field,0,0) : g in Generators(G)]>);
        A`W := RSpace(field, Dimension(A`Wmod));
        A`V := A`W;
        A`GSet_to_axes := map<Ax -> A`W | i :-> A`W!0>;
        return A;
      end if;
      
      // otherwise, we must reduce to the Miyamoto group
      alg := RestrictToMiyamotoGroup(alg);
      
      axes := Domain(glue);
      tau_images := [ i@tau : i in axes];
      H := sub<G | tau_images>;
      
      subsp := RSpaceWithBasis([A`W.i : i in axes]);

      map := hom< subsp -> alg`W | [i@glue@alg`GSet_to_axes : i in axes]>;
      
      homg := hom< H -> Group(alg) | [< g, g@homg> : g in FewGenerators(H)]>;

      assert3 forall(t){ <v,g> : v in Basis(subsp), g in H |
                       ((A!v)*(g))`elt @map eq (alg!(v@map)*(g@homg))`elt };
        
      subalgs`subsps cat:= [* subsp *];
      if alg in subalgs`algs then
        pos := Position(subalgs`algs, alg);
      else
        subalgs`algs join:= {@ alg @};
        pos := #subalgs`algs;
      end if;
      Append(~subalgs`maps, <map, homg, pos>);
    end for;
    
    // Mark that we have glued in an algebra which contains a full shape
    Or(~shape_flags, flags);
  end if;
  
  // We have now glued in all the maximal subgroups we can.
  // We check the remaining subalgebras given by the shape and if they haven't already been covered, we glue them in too.
  
  for i in [1..#shape] do
    if shape_flags[i] then // We have already glued in a max which covers this.
      continue i;
    end if;

    orb, type := Explode(shape[i]);

    subsp := RSpaceWithBasis([ A`W.i : i in orb]);
    subalgs`subsps cat:= [* subsp *];

    path := Sprintf("%o/%o/%m/basic_algebras", library_location, fusion_table`directory, BaseRing(A));
    if ExistsPath(path) and Sprintf("%o.json", type) in ls(path) then
      alg := LoadPartialAxialAlgebra(Sprintf("%o/%o", path, type));
    else
      alg := ChangeField(LoadPartialAxialAlgebra(Sprintf("%o/%o/RationalField()/basic_algebras/%o", library_location, fusion_table`directory, type)), field);
    end if;
    if alg in subalgs`algs then
      pos := Position(subalgs`algs, alg);
    else
      subalgs`algs join:= {@ alg @};
      pos := #subalgs`algs;
    end if;

    // We need to find an isomorphism from the group of the basic algebra to the subgroup of A
    // By assumption, the basic algebras have their first and second elements as generating idempotents.
    
    a0 := orb[1]@tau;
    a1 := orb[2]@tau;
    
    alg_tau := alg`tau;    
    alg_a0 := 1@alg_tau;
    alg_a1 := 2@alg_tau;

    // We find the involutions associated to the generating elements of the basic algebra, so we can identify the same rho
    
    D := sub<G | a0, a1>;
    homg := hom< D -> Group(alg) | [<a0, alg_a0>, <a1, alg_a1>]>;
    assert forall(t){ <g,h> : g,h in Generators(D) | (g*h)@homg eq (g@homg)*(h@homg)};

    alg_rho := alg_a0*alg_a1;
    if a0 ne G!1 and a1 ne G!1 then
      assert alg_rho eq (a0*a1) @ homg;
    else
      // There is at least one identity element
      assert type in {"2A", "2B"};
    end if;
    
    // We can now build the ordered basis.
    alg_bas := &join {@ {@ alg | alg.1*alg_rho^k, alg.2*alg_rho^k @} : k in [0..Order(alg_rho)-1] @};

    map := hom< subsp -> alg`W | Matrix(field, [ Eltseq(v) : v in alg_bas]) >;

    Append(~subalgs`maps, < map, homg, pos >);
  end for;

  A`subalgs := subalgs;
  A`V := sub<A`W|>;
  
  axis_classes := Sort({@ Representative(o) : o in Orbits(G, Ax) @});
  A`axes := [AssignAxis(A, Ax, tau, i) : i in axis_classes];

  A`mult := [];
  A`rels := {@ @};
  PullbackEigenvaluesAndRelations(New(ParAxlAlg), ~A: force_all:=true);
  
  // We force the grading and do the wh-w trick as we assume this has been done before an expansion
  A := ForceGrading(A);
  
  max_size := Max([#S : S in Keys(A`axes[1]`even)]);
  assert exists(evens){S : S in Keys(A`axes[1]`even) | #S eq max_size};
  
  for i in [1..#A`axes] do
    actionhom := GModuleAction(A`Wmod);
    Hmat := [ A`W_to_Wmod*(h@actionhom)*A`W_to_Wmod^-1 - IdentityMatrix(field, #Ax) : h in A`axes[i]`stab | h ne G!1];
    
    prods := [ FastMatrix({@ w : w in Basis(A`axes[i]`even[evens])@}, h) : h in Hmat];
    A`axes[i]`even[evens diff {@1@}] +:= sub< W | &join prods >;
  end for;
  
  return A;
end intrinsic;
/*

Assigns an axis

*/
intrinsic AssignAxis(A::ParAxlAlg, Ax::GSet, tau::Map, a::RngIntElt) -> Axis
  {
  Assigns the axes to A.
  }
  G := Group(A`Wmod);
  require G eq Group(Ax): "The group associated to W and the axes are not the same.";
  W := A`W;

  idem := New(AxlAxis);
  idem`id := A.a;
  H := Stabiliser(G, Ax, a);
  idem`stab := H;
  assert a@tau in Centre(H);
  idem`inv := a@tau;

  Ggr, gr := Grading(A`fusion_table);
  require Order(Ggr) in {1,2}: "The fusion table is not Z_2-graded.";

  idem`odd := AssociativeArray();
  idem`even := AssociativeArray();
  eigenvalues := A`fusion_table`eigenvalues;

  if Order(Ggr) eq 2 then
    preim := { lambda : lambda in eigenvalues | lambda @ gr eq Ggr.1 };
    for S in { IndexedSet(S) : S in Subsets(preim) | S ne {} } do
      idem`odd[S] := sub<W|>;
    end for;
  end if;

  preim := { lambda : lambda in eigenvalues | lambda @ gr eq Ggr!1 };
  for S in Subsets(preim) do
    idem`even[Sort(IndexedSet(S), EigenvalueSort)] := sub<W|>;
  end for;
  idem`even[{1}] := sub<W | idem`id`elt>;

  return idem;
end intrinsic;
/*
intrinsic NewGInvariantSubspace(WH::ModGrp, W::ModTupFld, S::.) -> ModTupFld
  {
  Returns the subspace of W spanned by S which is invariant under the action of the group associated to the G-module WH.
  }
  t := Cputime();
  require Type(S) in {SetIndx, SetEnum, SeqEnum}: "The given elements are not in a set or sequence.";
  if Type(Universe(S)) eq ParAxlAlg then
    SS := {@ s`elt : s in S @};
  elif Type(Universe(S)) eq ModTupFld then
    SS := S;
  elif Type(Universe(S)) eq ModGrp then
    SS := S;
  else
    error "S is not a set of vectors or partial axial algebra elements.";
  end if;
  require forall{ s : s in SS | IsCoercible(WH,s)}: "The set of elements given are not coercible into the given G-module.";
  
  Hmat := [ Matrix(h) : h in MatrixGroup(WH)];
  
  oldU := sub<W|>;
  newU := sub<W|S>;
  while oldU ne newU do
    oldU := newU;
    newU +:= sub<W| &join [ FastMatrix({@ v : v in Basis(newU)@}, h) : h in Hmat]>;
  end while;
  
  if Cputime(t) ge 1 then
    vprintf ParAxlAlg, 4: "Time taken for GInvariantSubspace is %o.  Starting number of objects %o, ending dim %o.\n", Cputime(t), #S, Dimension(newU);
  end if;
  return newU;
end intrinsic;
*/
intrinsic GInvariantSubspace(A::ParAxlAlg, S::.) -> ModTupFld
  {
  Returns the subspace of A spanned by S which is invariant under the action of the automorphism group of A.
  }
  t := Cputime();
  require Type(S) in {SetIndx, SetEnum, SeqEnum}: "The given elements are not in a set or sequence.";
  W := A`W;
  Wmod := A`Wmod;
  W_to_Wmod := A`W_to_Wmod;

  if #S eq 0 then
    return sub<W|>;
  end if;
  if Type(Universe(S)) eq ParAxlAlg then
    SS := FastMatrix({@ s`elt : s in S @}, W_to_Wmod);
  elif Type(Universe(S)) in {ModTupFld, ModGrp} then
    SS := FastMatrix(S, W_to_Wmod);
  else
    error "S is not a set of vectors or partial axial algebra elements.";
  end if;
  // Coercion can be a bit expensive
  // require forall{ s : s in SS | IsCoercible(Wmod,s)}: "The set of elements given are not coercible into the given G-module.";
  U := sub<Wmod | SS>;
  UU := sub< W | Rows(Matrix([W | W!Vector(Wmod!u) : u in Basis(U)])*W_to_Wmod^-1)>;
  if Cputime(t) ge 1 then
    vprintf ParAxlAlg, 4: "Time taken for GInvariantSubspace is %o.  Starting number of objects %o, ending dim %o.\n", Cputime(t), #S, Dimension(UU);
  end if;
  return UU;
end intrinsic;
/*
intrinsic GInvariantSubspace(WH::GModDec, W::ModTupFld, S::.) -> ModTupFld
  {
  Returns the subspace of W spanned by S which is invariant under the action of the group associated to the G-module WH.
  }
  t := Cputime();
  require Type(S) in {SetIndx, SetEnum, SeqEnum}: "The given elements are not in a set or sequence.";
  if #S eq 0 then
    return sub<W|>;
  end if;
  if Type(Universe(S)) eq ParAxlAlg then
    SS := FastMatrix({@ s`elt : s in S @}, ;
  elif Type(Universe(S)) eq ModTupFld then
    SS := S;
  elif Type(Universe(S)) eq ModGrp then
    SS := S;
  else
    error "S is not a set of vectors or partial axial algebra elements.";
  end if;
  require forall{ s : s in SS | IsCoercible(WH,s)}: "The set of elements given are not coercible into the given G-module.";
  U := sub<WH | SS>;
  UU := sub< W | [W | W!Vector(WH!u) : u in Basis(U)]>;
  if Cputime(t) ge 1 then
    vprintf ParAxlAlg, 4: "Time taken for GInvariantSubspace is %o.  Starting number of objects %o, ending dim %o.\n", Cputime(t), #S, Dimension(UU);
  end if;
  return UU;
end intrinsic;
*/
// Tests seem to show this is slower for A6 at about 4000 dim
/*
intrinsic InduceGInvariantSubspace(Wmod::ModGrp, W::ModTupFld, S::., H::Grp) -> ModTupFld
  {
  Given a collection S which is invariant under the action of the group H, induce to a submodule of Wmod, where H \leq Group(Wmod), and return as a subspace of W.
  }
  t := Cputime();
  require Type(S) in {SetIndx, SetEnum, SeqEnum}: "The given elements are not in a set or sequence.";
  if #S eq 0 then
    return sub<W|>;
  end if;

  // Dedupe S and make it a sequence
  time SS := Setseq(Set(S));

  if Type(Universe(SS)) eq ParAxlAlg then
    SS := Matrix([ s`elt : s in SS ]);
  elif ISA(Type(Universe(SS)), {ModTupFld, ModGrp}) then
    SS := Matrix(SS);
  else
    error "S is not a set of vectors or partial axial algebra elements.";
  end if;
  
  time SS := EchelonForm(SS);
  
  trans := Transversal(Group(Wmod), H);
  time actionhom := GModuleAction(Wmod);
  
  time newvects := [ SS*(g@actionhom) : g in trans];
  
  time U := sub<W | Flat([Rows(M) : M in newvects])>;
  
  if Cputime(t) ge 1 then
    vprintf ParAxlAlg, 4: "Time taken for InduceGInvariantSubspace is %o.  Starting number of objects %o, ending dim %o.\n", Cputime(t), #S, Dimension(U);
  end if;
  return U;
end intrinsic;
*/
//
// ================ UPDATE A PARTIAL AXIAL ALGEBRA ================
//
/*

Internal function for updating the axes.

*/
intrinsic UpdateAxes(A::ParAxlAlg, ~Anew::ParAxlAlg, psi::Map: matrix := Matrix(BaseRing(A), Dimension(A), Dimension(Anew), [u@psi : u in Basis(A`W)]))
  {
  If psi is a map from the subspace for A to the subspace for Anew, then build the axes for Anew from those of A.  NB we require psi to be a G-invariant map (although it is given as a map on the subspaces).  Takes an optional argument of the matrix of psi.
  }
  dims := CheckEigenspaceDimensions(A);

  // We collect up all the basis vectors for all the eigenspaces and find their images all at once
  allkeys := AssociativeArray();
  allkeys["even"] := IndexedSet(Keys(A`axes[1]`even));
  allkeys["odd"] := IndexedSet(Keys(A`axes[1]`odd));
  L := &cat[ Basis(A`axes[i]``attr[k]) : k in allkeys[attr], attr in ["even", "odd"], i in [1..#A`axes]];
  
  images := FastFunction(L, psi: matrix:=matrix);

  Wnew := Anew`W;
  axes := [];
  offset := 0;
  for i in [1..#A`axes] do
    newaxis := New(AxlAxis);
    newaxis`stab := A`axes[i]`stab;
    newaxis`inv := A`axes[i]`inv;
    newaxis`id := Anew!((A`axes[i]`id)`elt @ psi);
    
    for attr in ["even", "odd"] do
      newaxis``attr := AssociativeArray();
      for k in allkeys[attr] do
        // Since psi is G-invariant, we do not need to do GInvariantSubspace
        newaxis``attr[k] := sub<Wnew | images[offset+1..offset+Dimension(A`axes[i]``attr[k])]>;
        offset +:= Dimension(A`axes[i]``attr[k]);
      end for;
    end for;   
    Append(~axes, newaxis);
  end for;
  Anew`axes := axes;
end intrinsic;
/*

Internal function to update the subalgebras.

*/
intrinsic UpdateSubalgebras(A::ParAxlAlg, ~Anew::ParAxlAlg, psi::Map : algs := A`subalgs`algs, maps := A`subalgs`maps)
  {
  If psi is a map from the subspace for A to the subspace for Anew, then build the subalgebras for Anew from those of A.  We require psi to be G-invariant.  If given, algs is a list of new subalgebras and maps is a list of the corresponding new maps.
  }
  W := A`W;
  Wnew := Anew`W;
  newsubsps := [* *];
  newmaps := [* *];
  
  for i in [1..#A`subalgs`subsps] do
    subsp := A`subalgs`subsps[i];
    map, homg, pos := Explode(maps[i]);
    alg := algs[pos];

    // We calculate the restriction of psi to subsp so we ensure that the preimage of newsubsp lies in subsp
  
    psi_rest := hom<subsp->Wnew | [ v@psi : v in Basis(subsp)]>;
    
    require Dimension((Kernel(psi_rest)@map)) eq 0: "You need to quotient out the new subalgebra first.";

    newsubsp := sub<Wnew | [Wnew | u@psi_rest : u in Basis(subsp)]>;
    newmap := hom< newsubsp -> alg`W | [ u@@psi_rest@map : u in Basis(newsubsp)]>;
    Append(~newsubsps, newsubsp);
    Append(~newmaps, <newmap, homg, pos>);
  end for;
  
  subalgs := New(SubAlg);
  subalgs`subsps := newsubsps;
  subalgs`maps := newmaps;
  subalgs`algs := algs;
  Anew`subalgs := subalgs;
end intrinsic;
/*

Pull back the relations and eigenvectors from the subalgebras.

*/
intrinsic PullbackEigenvaluesAndRelations(A::ParAxlAlg, ~Anew::ParAxlAlg: force_all:=false)
  {
  Given a new partial axial algebra, Anew, pull back the relations and eigenvectors from its subalgebras.  If the option force_all is true, then we do this for all eigenvectors.  If false, then we just do it for those eigenvectors seen in the gluing maps of Anew, but not A.
  }
  Ggr := Anew`fusion_table`group;
  grading := Anew`fusion_table`grading;
  evals := Anew`fusion_table`eigenvalues;
  require Order(Ggr) le 2: "The algebra is more than Z_2-graded.";
  
  allkeys := AssociativeArray();
  allkeys["even"] := Subsets({@ e : e in evals | e@grading eq Ggr!1@});
  allkeys["odd"] := Subsets({@ e : e in evals | e@grading eq Ggr.1@}: empty := false);
  
  G := Group(Anew);
  Wnew := Anew`W;
  all_axes := Image(Anew`GSet_to_axes);
  
  for i in [1..#Anew`subalgs`subsps] do
    newmap, homg, pos := Explode(Anew`subalgs`maps[i]);
    alg := Anew`subalgs`algs[pos];
    
    vprint ParAxlAlg, 4: "Collecting relations";
    // We could either use GInvariantSubspace here or InduceGAction.
    // Sometimes InduceGAction is much longer than just forming a G-submodule.
    // But often it is a bit quicker, but not that much.  Don't really understand this.
    /*
    time U := GInvariantSubspace(Anew`Wmod, Wnew, Basis(Kernel(newmap)));
    time bas := {@ Wnew | u : u in &cat InduceGAction(G, Group(alg)@homg, actionhom, Basis(Kernel(newmap))) @};
    assert sub<Wnew | bas> eq U;
    */
    U := GInvariantSubspace(Anew, Basis(Kernel(newmap)));
    Anew`rels join:= {@ Wnew | u : u in Basis(U)@};
    
    Im_sp := Image(newmap);
    
    // if we are forcing all eigenvalues to be pulled back, then 
    if force_all then
      Im_old := sub<alg`W|>;
    else
      Im_old := Image(A`subalgs`maps[i,1]);
    end if;
    
    if Dimension(Im_sp) eq Dimension(Im_old) then
      continue;
    end if;
    vprint ParAxlAlg, 4: "Pulling back eigenvectors from the subalgebra.";
    
    // NB Im_sp is a G'-submodule of alg, where G' = Group(alg).  If an axis id of A is conjugate to an axis of alg by g, then the double coset KgG', where K = Stab(id) are all the elements which conjugate id to an axis of alg (of a given type). There could be additional outer automorphisms of alg induced by G, but we would see these in A and they would just fuse classes of axes in alg.  So, we need only find a single g to conjugate the eigenspaces.

    if not assigned axes then
      axes := [ Position(all_axes, Anew`axes[j]`id`elt) : j in [1..#Anew`axes]];
    end if;
    
    alg_axes := [ [j : j in [1..#all_axes] | all_axes[j] in Domain(newmap) and all_axes[j]@newmap eq alg`axes[k]`id`elt][1] : k in [1..#alg`axes]];
    
    // S is a set of tuples <j,k,g>, where the jth axis of Anew conjugates via g to the k^th axis of alg
    S := {@ <j,k,g> : j in [1..#Anew`axes], k in [1..#alg`axes] | so
              where so, g := IsConjugate(G, Anew`GSet, axes[j], alg_axes[k]) @};
         
    // Precompute the pullback matrix from Im_sp to Wnew
    pullback_mat := Matrix([(Basis(Im_sp)[l])@@newmap : l in [1..Dimension(Im_sp)]]);
    
    for s in S do
      j,k,g := Explode(s);
      // gather together all the eigenvectors needed and precompute the maps required
      // We only need to do those which are in Im_sp, but not Im_old
      
      eigvects := [];
      dims := AssociativeArray();
      for attr in ["even", "odd"], key in allkeys[attr] do
        eig_old := alg`axes[k]``attr[key] meet Im_old;
        bas := ExtendBasis(eig_old, alg`axes[k]``attr[key] meet Im_sp);
        dims[key] := #bas - Dimension(eig_old);
        eigvects cat:= [ Coordinates(Im_sp, v) : v in bas[Dimension(eig_old)+1..#bas]];
      end for;
      
      // We could have no new eigenvectors
      if #eigvects eq 0 then
        continue s;
      end if;

      // We don't want to use GModuleAction      
      // first pullback our eigenvectors and map to Wmod
      Wmodvects := Matrix(eigvects)*pullback_mat*Anew`W_to_Wmod;
      Wmodvects := ChangeUniverse(RowSequence(Wmodvects), Anew`Wmod);
      
      H := (alg`axes[k]`stab@@homg)^(g^-1);
      Htrans := Transversal(Anew`axes[j]`stab, H);
      
      newvects := [ Wmodvects*(g^-1*h) : h in Htrans];
      
      // now we push all of these back to W
      newvects := Matrix([ Vector(w) : w in newvects[i], i in [1..#newvects]])*Anew`W_to_Wmod^-1;
      
      offset := 0;
      for attr in ["even", "odd"], key in allkeys[attr] do
        seq := &cat[ [(j-1)*#eigvects + offset+1.. (j-1)*#eigvects + offset+dims[key]] : j in [1..#Htrans]];
        Anew`axes[j]``attr[key] +:= sub<Wnew | newvects[seq]>;
        offset +:= dims[key];
      end for;
    end for;
  end for;
end intrinsic;
