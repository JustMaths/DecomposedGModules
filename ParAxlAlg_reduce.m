/*

Axial algebra enumerator

These are functions to reduce the algebra

*/
/*

This function implements an automatic version of the algorithm:

1) ExpandSpace

2) i) ExpandOdd

  ii) ExpandEven

Check to see if Dim(V) = Dim(W) and if not goto (1) and repeat.

There is a dimension limit where if W exceeds this then it won't be expanded further the procedure exits

*/
intrinsic AxialReduce(A::ParAxlAlg: dimension_limit := 150, backtrack := false, stabiliser_action := true, reduction_limit:= func<A | Maximum(Floor(Dimension(A)/4), 50)>) -> ParAxlAlg, BoolElt
  {
  Performs ExpandEven and ExpandSpace repeatedly until either we have completed, or the dimension limit has been reached.
  }
  if Dimension(A) eq 0 then
    return A;
  end if;

  while Dimension(A) ne Dimension(A`V) and Dimension(A) le dimension_limit do
  
    // First we expand
    AA, phi := ExpandSpace(A: implement:= false, stabiliser_action := stabiliser_action);
    
    // If we are backtracking and there is some intersection then form a new A and continue
    if backtrack and Dimension(sub<AA`W | AA`rels> meet AA`V) ne 0 then
      vprint ParAxlAlg, 4: "Backtracking...";
      U := sub<AA`W | AA`rels>;
      pullback := Matrix([ (AA`V).i@@phi : i in [1..Dimension(AA`V)]]);
      Coeffs := [ Coordinates(AA`V, v) : v in Basis(U meet AA`V)];
      Upullback := sub<A`W | FastMatrix(Coeffs, pullback)>;
      Upullback := SaturateSubspace(A, Upullback);
      A := ReduceSaturated(A, Upullback);
      continue;
    end if;
    
    // We have no more intersection found
    if Dimension(AA) ne 0 then
      AA, psi := ImplementRelations(AA);
      phi := phi*psi;
    end if;
    if Dimension(AA) eq 0 then
      A := AA;
      break;
    end if;
    
    // Now we reduce the even part    
    AA := ExpandEven(AA: reduction_limit:=reduction_limit(AA), backtrack := backtrack);
    
    // If we are backtracking and there is some intersection then form a new A and continue
    if backtrack and Dimension(sub<AA`W|AA`rels> meet AA`V) ne 0 then
      vprint ParAxlAlg, 4: "Backtracking...";
      U := sub<AA`W | AA`rels>;
      pullback := Matrix([ (AA`V).i@@phi : i in [1..Dimension(AA`V)]]);
      Coeffs := [ Coordinates(AA`V, v) : v in Basis(U meet AA`V)];
      Upullback := sub<A`W | FastMatrix(Coeffs, pullback)>;
      Upullback := SaturateSubspace(A, Upullback);
      A := ReduceSaturated(A, Upullback);
      continue;
    end if;
    
    // There is nothing to backtrack to
    if Dimension(AA) ne 0 and #AA`rels ne 0 then
      A := ImplementRelations(AA);
    else
      A := AA;
    end if;
  end while;

  if Dimension(A) eq Dimension(A`V) then
    vprint ParAxlAlg, 1: "Reduction complete!";
    return A, true;
  else
    vprintf ParAxlAlg, 1: "Reduction failed. Dimension of A is %o, dimension of V is %o.\n", Dimension(A), Dimension(A`V);
    return A, false;
  end if;
end intrinsic;
/*

We provide a function to do all shapes for a given group

*/
intrinsic ShapeReduce(G::Grp: saves:=true, starting_position := 1, fusion_table := MonsterFusionTable(), field := Rationals(), subgroups := "maximal", partial := false, shape_stabiliser := true, dimension_limit := 150, backtrack := false, stabiliser_action := true, reduction_limit:= func<A | Maximum(Floor(Dimension(A)/4), 50)>) -> SeqEnum
  {
  Given a group G, find all the shapes, build the partial algebras and reduce.
  }
  shapes := Shapes(G);
  require starting_position le #shapes: "Starting position is greater than the number of shapes.";
  vprintf ParAxlAlg, 1: "Found %o shapes for the group.\n", #shapes;
  output := [];
  for i in [starting_position..#shapes] do
    vprintf ParAxlAlg, 1: "Beginning shape %o of %o.\n", i, #shapes;
    vprintf ParAxlAlg, 1: "Partial algebra has %o axes of shape %o.\n", #shapes[i,1], shapes[i,3];
    A := PartialAxialAlgebra(shapes[i]: fusion_table:=fusion_table, field:=field, subgroups:=subgroups, partial:=partial, shape_stabiliser:=shape_stabiliser);
    t := Cputime();
    A := AxialReduce(A: dimension_limit:=dimension_limit, backtrack:=backtrack, stabiliser_action:=stabiliser_action, reduction_limit:=reduction_limit);
    Append(~output, A);
    vprintf ParAxlAlg, 4: "\nTime taken for complete reduction %o.\n\n", Cputime(t);
    if saves then
      SavePartialAxialAlgebra(A);
    end if;
  end for;

  return output;
end intrinsic;
//
// =============== REDUCING AN ALGEBRA ===================
//
/*

U is a subspace which we want to mod out by.  Therefore we may also mod out by v*u for any u in U and v in V.  We grow the subspace U by doing this.

*/
intrinsic SaturateSubspace(A::ParAxlAlg, U::ModTupRng: starting := sub<A`W|>) -> ModTupRng
  {
  Add products of U \cap V with V to U until it saturates, also using the action of G.  Has an optional argument of a starting subspace which we assume to be saturated.
  }
  t := Cputime();
  // The expensive part is doing coercion from a G-submod to Wmod in order to coerce into W
  // We minimise the amount of coercion by working in the G-submods as much as possible and only coercing all the vectors in U - U\cap V at the very end.
  
  W := A`W;
  require U subset W: "The given U is not a subspace of W.";
  Wmod := A`Wmod;
  W_to_Wmod := A`W_to_Wmod;
  V := A`V;
  Vmod := sub<Wmod | Rows(BasisMatrix(V)*W_to_Wmod)>;
  
  Umod := sub<Wmod| Rows(BasisMatrix(U)*W_to_Wmod)>;
  Dmod_old := sub<Wmod| Rows(BasisMatrix(starting meet V)*W_to_Wmod)>;
  Dmod_new := Umod meet Vmod;
  
  if Dimension(Umod) eq Dimension(U) then
    // U was already given as a G_Invariant space.
    bas := Basis(U);
    Uorig := Umod;
  end if;
  
  while Dimension(Dmod_new) gt Dimension(Dmod_old) do
    vprintf ParAxlAlg, 1: "Saturate subspace: Dimension intersection with V is %o\n", Dimension(Dmod_new);
    tt := Cputime();
    // We only do products of V with the new vectors found in D
    basmod_new := ExtendBasis(Dmod_old, Dmod_new)[Dimension(Dmod_old)+1..Dimension(Dmod_new)];
    
    bas_new := FastMatrix([ W | W!Vector(Wmod!u) : u in basmod_new], W_to_Wmod^-1);
    
    S := IndexedSet(&cat BulkMultiply(A, bas_new, Basis(V)));
    
    ttt := Cputime();
    Q, phi := quo<Wmod | Umod>;
    phimat := QuoMap(Wmod, Umod);
    phi := hom< W -> VectorSpace(Q) | phimat>;
    if Dimension(Image(phimat)) ne 0 then
      SQ := FastMatrix(S, W_to_Wmod*phimat);
    else // We have killed everything.
      SQ := [];
    end if;
    UU := sub<Q | SQ>;
    Usp := sub<VectorSpace(Q) | [VectorSpace(Q) | Vector(Q!v) : v in Basis(UU)]>@@phi;
    Umod := sub< Wmod | [ Wmod | u : u in Basis(Usp)]>;
    vprintf ParAxlAlg, 4: "    Time taken for new quotient method %o\n", Cputime(ttt);
    
    Dmod_old := Dmod_new;
    Dmod_new := Umod meet Vmod;
    vprintf ParAxlAlg, 4: "  Time taken %o\n", Cputime(tt);
  end while;
  
  // Check whether we started with a saturated U and hence can coerce back quicker.
  if assigned Uorig then
    extras := ExtendBasis(Uorig, Umod)[Dimension(Uorig)+1..Dimension(Umod)];
    extras := FastMatrix([ W | Vector(Wmod!u) : u in extras], W_to_Wmod^-1);
    U := sub<W | bas cat extras>;
  
    vprintf ParAxlAlg, 4: "Time taken for saturate subspace %o\n", Cputime(t);
    return U;
  end if;
  
  U := sub<W | FastMatrix([W | W!Vector(Wmod!u) : u in Basis(Umod)], W_to_Wmod^-1)>;
    
  vprintf ParAxlAlg, 4: "Time taken for saturate subspace %o\n", Cputime(t);
  return U;
end intrinsic;

intrinsic ReduceSaturated(A::ParAxlAlg, U::ModTupFld) -> ParAxlAlg, Map
  {
  Construct the algebra G-module W/U for a saturated U.
  }
  t := Cputime();
  W := A`W;
  Wmod := A`Wmod;
  W_to_Wmod := A`W_to_Wmod;
  V := A`V;

  Anew := New(ParAxlAlg);
  Anew`GSet := A`GSet;
  Anew`tau := A`tau;
  Anew`shape := A`shape;
  Anew`number_of_axes := A`number_of_axes;
  Anew`fusion_table := A`fusion_table;
  Anew`group := A`group;
  Anew`Miyamoto_group := A`Miyamoto_group;

  if Dimension(U) eq Dimension(A) then
    Wnew, psi := quo<W | W>;
    Anew`W := Wnew;
    Anew`Wmod := quo<Wmod | Wmod >;
    Anew`V := V @ psi;
    Anew`GSet_to_axes := map<Anew`GSet -> Wnew | [<i, Wnew!0> : i in Anew`GSet]>;
    
    vprintf ParAxlAlg, 4: "Time taken for ReduceSaturated %o\n", Cputime(t);
    return Anew, psi;
  end if;
  
  if assigned A`subalgs then
    tt := Cputime();
    // We create new algebras and maps as we might have to change the algebras to quotients.
    newalgs := A`subalgs`algs;
    newmaps := A`subalgs`maps;
    
    subalgs_intersections := { i : i in [1..#newmaps] | not (A`subalgs`subsps[i] meet U) subset Kernel(newmaps[i,1])};
    extras := sub<W|>;
    while subalgs_intersections ne {} do
      for i in subalgs_intersections do
        subsp := A`subalgs`subsps[i];
        map, homg, pos := Explode(newmaps[i]);
        alg := newalgs[pos];
        
        U_alg := (U meet subsp)@map;
        
        U_alg := SaturateSubspace(alg, U_alg);
        vprint ParAxlAlg, 3: "Reducing the subalgebra.";
        alg_new, quo_alg := ReduceSaturated(alg, U_alg);

        if Dimension(alg_new) eq 0 then
          // We have killed the entire subalgebra and hence modded out A by some axes.

          Wnew, psi := quo<W | W>;
          Anew`W := Wnew;
          Anew`Wmod := quo<Wmod | Wmod >;
          Anew`V := V @ psi;
          Anew`GSet_to_axes := map<Anew`GSet -> Wnew | [<i, Wnew!0> : i in Anew`GSet]>;
          
          vprintf ParAxlAlg, 4: "Time taken for ReduceSaturated %o\n", Cputime(t);
          return Anew, psi;
        else
          // There is a non-trivial quotient of the subalgebra
          
          // First check to see if the old alg is not used in another map
          if #[ t[3] : t in newmaps | t[3] eq pos] eq 1 then
            if alg_new notin newalgs then
              newalgs := newalgs[1..pos-1] join {@ alg_new @} join newalgs[pos+1..#newalgs];
              // all the numberings for pos are fine
            else
              newalgs := newalgs[1..pos-1] join newalgs[pos+1..#newalgs];
              // need to update all the other numberings for pos
              for j in { j : j in [1..#newmaps] | newmaps[j,3] gt pos} do
                newmaps[j,3] -:= 1;
              end for;
              pos := Position(newalgs, alg_new);
            end if;
          else
            // The old alg is still used
            Include(~newalgs, alg_new);
            pos := Position(newalgs, alg_new);
          end if;
          newmaps[i] := < map*quo_alg, homg, pos>;
          
          // We pull back any new relations from the subalgebra
          extras +:= Kernel(quo_alg) @@ map;
        end if;
      end for;
      if Dimension(extras) gt 0 then
        U := SaturateSubspace(A, U+extras: starting := U);
      end if;
      subalgs_intersections := { i : i in [1..#newmaps] | not (A`subalgs`subsps[i] meet U) subset Kernel(newmaps[i,1])};
    end while;
    
    vprintf ParAxlAlg, 4: "Time taken for collecting info from subalgebras %o\n", Cputime(tt);
  end if;

  // We have grown U as much as possible, so now we form the quotient
  tt := Cputime();

  // To get the matrix quickly, we go through this silly workaround to use a reduced form module rather than a vectorspace.
  Wnew, psi := quo<KModule(BaseRing(A), Dimension(A))|U>;
  Wnew := VectorSpace(Wnew);
  psi_mat := MapToMatrix(psi);
  psi := hom< W-> Wnew | psi_mat>;

  // For Wmod
  Umodbas := FastMatrix(Basis(U), W_to_Wmod);
  Anew`Wmod, psi_mod := quo<Wmod | Umodbas >;
  psi_mod_mat := QuoMap(Wmod, Umodbas);
  
  // Find the induced map Anew`W to Anew`Wmod
  // instead of taking the pre-image, calculate the Echelon form
  _, preims := EchelonForm(psi_mat);
  
  assert3 forall(err){i : i in [1..Dimension(Wnew)] | Support(preims[i]@psi) eq {i}};
  preims := RowSubmatrix(preims, Dimension(Wnew));
  
  Anew`W_to_Wmod := preims*W_to_Wmod*psi_mod_mat;
  
  Anew`W := Wnew;
  Anew`V := V @ psi;
  
  if Dimension(Wnew) eq 0 then
    Anew`GSet_to_axes := map<Anew`GSet -> Wnew | i :-> Wnew!0>;
    Anew`rels := {@ W | @};
    vprintf ParAxlAlg, 4: "Time taken for ReduceSaturated %o\n", Cputime(t);
    return Anew, psi;
  end if;
  
  images := FastMatrix(Image(A`GSet_to_axes), psi_mat);
  Anew`GSet_to_axes := map<Anew`GSet -> Wnew | [ <i, images[i]> : i in Anew`GSet]>;
  
  vprintf ParAxlAlg, 4: "Time taken to build modules and vector spaces %o.\n", Cputime(tt);
  vprintf ParAxlAlg, 4: "Module dimension is %o.\n", Dimension(Anew`W);
  
  tt := Cputime();  
  UpdateAxes(A, ~Anew, psi: matrix := psi_mat);
  vprintf ParAxlAlg, 4: "Time taken to update axes %o\n", Cputime(tt);
  
  tt := Cputime();
  if assigned newalgs then
    UpdateSubalgebras(A, ~Anew, psi: algs := newalgs, maps:=newmaps);
  else
    UpdateSubalgebras(A, ~Anew, psi);
  end if;
  vprintf ParAxlAlg, 4: "Time taken to update subalgebras %o\n", Cputime(tt);
  
  // We calculate the restriction of psi to V so we ensure that the preimage of Vnew lies in V
  tt := Cputime();  
  psi_rest := hom<V->Wnew | [ v@psi : v in Basis(V)]>;

  vprint ParAxlAlg, 2: "  Calculating the new multiplication table.";
  V_new_pullback := [ W | u@@ psi_rest : u in Basis(Anew`V) ];
  
  decompV := [Coordinates(V, v) : v in V_new_pullback];
  prods := FastMatrix(BulkMultiply(A, decompV), psi_mat);
  
  Anew`mult := [ [ Wnew | ] : i in [1..Dimension(Anew`V)]];
  for i in [1..Dimension(Anew`V)], j in [1..i] do
    Anew`mult[i,j] := prods[i*(i-1) div 2 +j];
    Anew`mult[j,i] := Anew`mult[i,j];
  end for;
  vprintf ParAxlAlg, 4: "  Time taken %o\n", Cputime(tt);
  
  vprint ParAxlAlg, 2: "  Mapping the remaining relations into the new W.";
  tt := Cputime();
  Anew`rels := {@ v : v in FastMatrix(A`rels, psi_mat) | v ne Wnew!0 @};
  vprintf ParAxlAlg, 4: "  Time taken %o\n", Cputime(tt);
  
  vprintf ParAxlAlg, 4: "Time taken for ReduceSaturated %o\n", Cputime(t);
  return Anew, psi;
end intrinsic;
/*

We use the following to impose the relations on the algebra that we have built up to reduce it.

*/
intrinsic ImplementRelations(A::ParAxlAlg: max_number:=#A`rels) -> ParAxlAlg, Map
  {
  Implement the relations we have built up.
  }
  t:=Cputime();
  Anew := A;

  phi := hom<A`W -> A`W | Morphism(A`W, A`W)>;
  while assigned Anew`rels and #Anew`rels ne 0 do
    vprintf ParAxlAlg, 1: "Dim(A) is %o, Dim(V) is %o, number of relations is %o.\n", Dimension(Anew), Dimension(Anew`V), #Anew`rels;
    U := SaturateSubspace(Anew, sub<Anew`W| Anew`rels[1..Minimum(max_number, #Anew`rels)]>);
    Anew, phi_new := ReduceSaturated(Anew, U);
    phi := phi*phi_new;
  end while;

  vprintf ParAxlAlg, 1: "Dim(A) is %o, Dim(V) is %o.\n", Dimension(Anew), Dimension(Anew`V);
  vprintf ParAxlAlg, 4: "Time taken for ImplementRelations %o\n", Cputime(t);
  return Anew, phi;
end intrinsic;
//
// ================ EXPANDING AN ALGEBRA ====================
//
/*

Implements an inner product for G-modules.

*/
intrinsic GetInnerProduct(W:ModGrp) -> AlgMatElt
  {
  Finds an inner product which is compatible with the G-module structure.
  }
  G := Group(W);
  phi := GModuleAction(W);

  return &+[ Matrix(g*Transpose(g)) where g := h@phi : h in G];
end intrinsic;
/*

Finds complements in G-modules.

*/
intrinsic Complement(W::ModGrp, U::ModGrp: ip:=GetInnerProduct(W)) -> ModGrp
  {
  Finds the complement of U inside W.  Takes an optional argument of a Matrix which is the Gram matrix of an inner product.  This defaults to calculating a G-invariant inner product using GetInnerProduct(W).
  }
  require U subset W: "U is not a submodule of W";
  U_bas := [(W!v) : v in Basis(U)];
  if #U_bas eq 0 then
    return W;
  else
    return sub<W | [W!v : v in Basis(NullSpace(Transpose(Matrix(U_bas)*ip)))]>;
  end if;
end intrinsic;
/*

Decomposes with respect to an inner product correctly! magma only does the standard inner product...

*/
intrinsic DecomposeVectorWithInnerProduct(U::., v::.: ip := GetInnerProduct(Parent(v)), Minv := (Matrix(Basis(U))*ip*Transpose(Matrix(Basis(U))))^-1) -> ., .
  {
  Return the unique u in U and w in the complement of U such that v = u + w.  Defaults to calculating a G-invariant inner product using GetInnerProduct(W).
  }
  require Type(U) in {ModTupFld, ModGrp}: "The space given is not a module or a vector space.";
  W := Parent(v);
  require U subset W: "U is not a submodule of W";
  if Dimension(U) eq 0 then
    return W!0, v;
  end if;
  U_bas := [(W!u) : u in Basis(U)];
  
  vU := v*ip*Transpose(Matrix(U_bas))*Minv*Matrix(U_bas);

  return vU, v-vU;
end intrinsic;

intrinsic DecomposeVectorsWithInnerProduct(U::., L::.: ip := GetInnerProduct(Parent(L[1]))) -> SeqEnum
  {
  For a SetIndx L of vectors v, return a set of tuples <vU, vC> where v = vU + vC is the decomposition into V = U + U^\perp, with respect to an arbitrary inner product.
  }
  require Type(L) in {SeqEnum, SetIndx, List}: "The collection given is not ordered.";
  require Type(U) in {ModTupFld, ModGrp}: "The space given is not a module or a vector space.";
  W := Universe(L);
  require U subset W: "U is not a submodule of W";
  if Dimension(U) eq 0 then
    return [ < W!0, v> : v in L];
  end if;
  U_bas := [(W!v) : v in Basis(U)];
  M := ip*Transpose(Matrix(U_bas))*(Matrix(U_bas)*ip*Transpose(Matrix(U_bas)))^-1*Matrix(U_bas);

  prods := FastMatrix([ l : l in L], M);

  return [ <prods[i], L[i]-prods[i]> : i in [1..#L]];
end intrinsic;

intrinsic InduceGAction(G::GrpPerm, H::GrpPerm, actionhom::Map, L::.) -> SeqEnum
  {
  Let L be the basis of a subspace which is H-invariant.  Return the G-invariant subspace spanned by L, where the action is given by actionhom.
  }
  t := Cputime();
  require Type(L) in {SeqEnum, SetIndx}: "The collections of elements must be a set or sequence.";
  if #L eq 0 then
    return L;
  end if;
  
  // We use matrices as they are faster
  if Type(L) eq SeqEnum then
    matrices := [Matrix(L)];
  else
    matrices := [Matrix(Setseq(L))];
  end if;
  
  for h in Transversal(G, H) diff {@ Id(G)@} do
    Append(~matrices, matrices[1]*(h@actionhom));
  end for;
  
  if Type(L) eq SeqEnum then
    vprintf ParAxlAlg, 4: "Induced G-action in time %o\n", Cputime(t);
    return [Rows(M) : M in matrices];
  else
    vprintf ParAxlAlg, 4: "Induced G-action in time %o\n", Cputime(t);
    return {@ IndexedSet(Rows(M)) : M in matrices @};
  end if;
end intrinsic;
/*

We wish to expand the space W

We write W = V + C where C is complement.  We then expand to W_new which is:

  S^2(C) + VxC + W

We do the new module in this order this tends to make W be preserved in the quotient when magma quotients out by relations w = x, where x is not in W.

*/
ijpos := function(i,j,n)
  if i le j then
    return &+[ n+1 -k : k in [0..i-1]] -n +j-i;
  else
    return &+[ n+1 -k : k in [0..j-1]] -n +i-j;
  end if;
end function;

intrinsic ExpandSpace(A::ParAxlAlg: implement := true, stabiliser_action := true) -> ParAxlAlg, Map
  {
  Let A = V \oplus C.  This function expands A to S^2(C) \oplus (V \otimes C) \oplus A, with the new V being the old A.  We then factor out by the known multiplications in old V and return the new partial axial algebra.
  }
  t := Cputime();
  require Dimension(A`W) ne Dimension(A`V): "You have already found the multiplication table to build a full algebra - no need to expand!";
  
  vprintf ParAxlAlg, 1: "Expanding algebra from %o dimensions.\n", Dimension(A);
  tt := Cputime();
  
  if Type(A`Wmod) eq ModGrp then
    // temporary
    A`Wmod, A`W_to_Wmod := DecomposedGModule(A`Wmod);
  end if;

  
  G := Group(A);
  W := A`W;
  Wmod := A`Wmod;
  W_to_Wmod := A`W_to_Wmod;
  V := A`V;

  // We build the modules and maps
  Vmod := sub<Wmod | Rows(BasisMatrix(A`V)*W_to_Wmod)>;
  Cmod := Complement(Wmod, Vmod);

  VCmod, VCmap := TensorProduct(Vmod, Cmod);
  C2mod, C2map := SymmetricSquare(Cmod);

  Wmodnew, injs := DirectSum([C2mod, VCmod, Wmod]);
  
  // We build the new change of basis map
  Vmodsp := RSpaceWithBasis([ A`W | Vector(Wmod!v) : v in Basis(Vmod)]);
  V_to_Vmod := Matrix([ VectorSpace(BaseRing(A), Dimension(V)) | Coordinates(Vmodsp, v) : v in Rows(BasisMatrix(A`V)*W_to_Wmod)]);

  C := sub< A`W | [A`W | v : v in Rows(Matrix([Vector(Wmod!c) : c in Basis(Cmod)])*W_to_Wmod^-1)]>;
  Cmodsp := RSpaceWithBasis([ A`W | Vector(Wmod!c) : c in Basis(Cmod)]);
  C_to_Cmod := Matrix([ Coordinates(Cmodsp, c) : c in Rows(BasisMatrix(C)*W_to_Wmod)]);

  if assigned VCmap then
    VC_to_VCmod := TensorProduct(V_to_Vmod, C_to_Cmod)*Matrix(Flat(VCmap));
  else
    VC_to_VCmod := ZeroMatrix(BaseRing(A), 0, 0);
  end if;
  C2_to_C2mod := SymmetricSquare(C_to_Cmod)*Matrix(Flat(C2map));

  Wnew_to_Wmodnew := DiagonalJoin(<C2_to_C2mod, VC_to_VCmod, W_to_Wmod>)*VerticalJoin(<injs[1], injs[2], injs[3]>);
  
  // We build the corresponding vector spaces and maps
  
  Wnew := RSpace(BaseRing(A), Dimension(Wmodnew));
  
  id := IdentityMatrix(BaseRing(W), Dimension(Wnew));
  C2toWnew_mat := RowSubmatrix(id, 1, Dimension(C2mod));
  VCtoWnew_mat := RowSubmatrix(id, Dimension(C2mod) + 1, Dimension(VCmod));
  WtoWnew_mat := RowSubmatrix(id, Dimension(C2mod) + Dimension(VCmod)+1, Dimension(W));

  WtoWnew := hom< W -> Wnew | WtoWnew_mat >;
    
  Anew := New(ParAxlAlg);
  Anew`GSet := A`GSet;
  Anew`tau := A`tau;
  Anew`shape := A`shape;
  images := FastMatrix(Image(A`GSet_to_axes), WtoWnew_mat);
  Anew`GSet_to_axes := map<Anew`GSet -> Wnew | [ <i, images[i]> : i in Anew`GSet]>;
  Anew`number_of_axes := A`number_of_axes;
  Anew`fusion_table := A`fusion_table;
  Anew`rels := {@ Wnew | @};
  Anew`group := A`group;
  Anew`Miyamoto_group := A`Miyamoto_group;
  
  Anew`Wmod := Wmodnew;
  Anew`W := Wnew;
  Anew`V := W@WtoWnew;
  Anew`W_to_Wmod := Wnew_to_Wmodnew;
  vprintf ParAxlAlg, 2: "Expanded to %o dimensions.\n", Dimension(Anew`W);
  vprintf ParAxlAlg, 4: "Time taken to build modules and vector spaces %o.\n", Cputime(tt);
  
  vprint ParAxlAlg, 2: "  Building the multiplication.";
  tt := Cputime();
  
  // First build the multiplication with repsect to the basis Basis(C)+Basis(V) and then do a change of basis into Basis(W)

  basV := Basis(V);
  basC := Basis(C);
  dimV := #basV;
  dimC := #basC;
  
  prodsV := FastMatrix(BulkMultiply(A, basV), WtoWnew_mat);
  
  mult := [[Wnew | ] : i in [1..Dimension(W)]];
  // We do in order, C then V
  for i in [1..Dimension(W)] do
    for j in [1..i] do
      if i le dimC then
        // So we are in S^2(C)
        mult[i][j] := C2toWnew_mat[ijpos(i,j,dimC)];
      else
        // So the ith vector is in V
        if j le dimC then
          // This is VC
          mult[i,j] := VCtoWnew_mat[(i-dimC-1)*dimC + j];
        else
          // This is V \otimes V
          mult[i,j] := prodsV[(i-dimC)*(i-1-dimC) div 2 + j-dimC];
        end if;
      end if;
      if j ne i then
        mult[j][i] := mult[i][j];
      end if;
    end for;
  end for;
  // Now we need to change basis
  CV_to_W := Rows(Matrix(basC cat basV)^-1);
  Anew`mult := BulkMultiply(mult, CV_to_W, CV_to_W);
  
  vprintf ParAxlAlg, 4: "  Time taken to build the multiplication table %o.\n", Cputime(tt);
  
  // We now build the axes
  vprint ParAxlAlg, 2: "  Updating the axes.";
  tt := Cputime();
  UpdateAxes(A, ~Anew, WtoWnew: matrix:=WtoWnew_mat);
  vprintf ParAxlAlg, 4: "  Time taken for updating the axes %o.\n", Cputime(tt);
  
  vprint ParAxlAlg, 2: "  Updating the odd and even parts.";
  tt := Cputime();
  // We now build the odd and even parts and do w*h-w
  
  max_size := Max([#S : S in Keys(A`axes[1]`even)]);
  assert exists(evens){S : S in Keys(A`axes[1]`even) | #S eq max_size};
  max_size := Max([#S : S in Keys(A`axes[1]`odd)]);
  assert exists(odds){S : S in Keys(A`axes[1]`odd) | #S eq max_size};

  for i in [1..#A`axes] do
    // For each axes, the new even part comes from the old even x even plus the old odd x odd.
    // Similarly for the new odd part
    // To speed up the calculation we will try to calculate a set of vectors which span and are as linearly independent as possible before building a subspace from them.
    // For the even case, we also want to remember which pairs we took to speed up the w*h-w trick

    // Decompose even subspace E into V meet E, C meet E and the rest N
    Ve := Basis(V meet A`axes[i]`even[evens]);
    Ce := Basis(C meet A`axes[i]`even[evens]);
    if Dimension(A`axes[i]`even[evens]) ne #Ve+#Ce then
      Ne := ExtendBasis(Ve cat Ce, A`axes[i]`even[evens])[#Ve+#Ce+1..Dimension(A`axes[i]`even[evens])];
    else
      Ne := [];
    end if;

    // Decompose the odd similarly
    Vo := Basis(V meet A`axes[i]`odd[odds]);
    Co := Basis(C meet A`axes[i]`odd[odds]);
    if Dimension(A`axes[i]`odd[odds]) ne #Vo+#Co then
      No := ExtendBasis(Vo cat Co, A`axes[i]`odd[odds])[#Vo+#Co+1..Dimension(A`axes[i]`odd[odds])];
    else
      No := [];
    end if;

    bas := Ve cat Ne cat Ce cat Vo cat No cat Co;
    nVe := 1;
    nNe := #Ve+nVe;
    nCe := #Ne+nNe;
    nVo := #Ce+nCe;
    nNo := #Vo+nVo;
    nCo := #No+nNo;
    // Find multiplication wrt the basis bas
    basmult := BulkMultiply(Anew`mult, bas, bas);

    // The even space is spanned by
    // W_e@WtoWnew_mat + (VeCe + NeCe) + (VoCo + NoCo) + NeNe + NoNo + CeCe + CoCo

    // Of these, the ones which must be linearly independent are anything without N
    // W_e@WtoWnew_mat + VeCe + VoCo + CeCe + CoCo

    even_pairs := [ <j,k> : k in [nCe..nVo-1], j in [nVe..nNe-1]]
          cat [ <j,k> : k in [nCo..#bas], j in [nVo..nNo-1]]
          cat [ <j,k> : k in [nCe..j], j in [nCe..nVo-1]]
          cat [ <j,k> : k in [nCo..j], j in [nCo..#bas]];

    even := FastMatrix(Basis(A`axes[i]`even[evens]), WtoWnew_mat)
          cat [ basmult[t[1], t[2]] : t in even_pairs];

    assert2 IsIndependent(even);

    // These could have linear depedences with the above
    // NeCe + NoCo + NeNe + NoNo
    even_poss_pairs := [ <j,k> : k in [nCe..nVo-1], j in [nNe..nCe-1]]
          cat [ <j,k> : k in [nCo..#bas], j in [nNo..nCo-1]]
          cat [ <j,k> : k in [nNe..j], j in [nNe..nCe-1]]
          cat [ <j,k> : k in [nNo..j], j in [nNo..nCo-1]];

    even_poss := [ basmult[t[1], t[2]] : t in even_poss_pairs];

    for j in [1..#even_poss_pairs] do
      if IsIndependent(even cat even_poss[j]) then
        Append(~even, even_poss[j]);
        Append(~even_pairs, even_poss_pairs[j]);
      end if;
    end for;

    Anew`axes[i]`even[evens] := sub<Wnew | even>;

    // For odd, we do not need to keep track of the pairs which give the basis vectors, so we just build all in the same way as above
    // W_o@WtoWnew_mat + (VeCo + NeCo) + (VoCe + NoCe) + (NeNo + NeCo + CeCo)
    odd := FastMatrix(Basis(A`axes[i]`odd[odds]), WtoWnew_mat)
          cat &cat[ basmult[i][nCo..#bas] : i in [nVe..nCe-1]]
          cat &cat[ basmult[i][nCe..nVo-1] : i in [nVo..nCo-1]]
          cat &cat[ basmult[i][nNe..nVo-1] : i in [nNo..#bas]];

    Anew`axes[i]`odd[odds] := sub<Wnew | odd>;

    if stabiliser_action then
      vprint ParAxlAlg, 2: "  Doing the w*h-w trick.";
      /*
      // now GModules are quick, try w*h-w the straightforward way

      H := Anew`axes[i]`stab;
      
      // precompute the images of all the basis vectors in the basis of bas
      // We don't want to use GModuleAction

      bas_mat := BasisMatrix(Anew`axes[i]`even[evens])*Anew`W_to_Wmod;
      basWmod := ChangeUniverse(RowSequence(bas_mat), Anew`Wmod);
      images := [ basWmod*h : h in H | h ne H!1];
      
      // now join these together and push to W
      images := Matrix([ Vector(w) : w in images[i], i in [1..#images]])*Anew`W_to_Wmod^-1;
      
      newvects := images - VerticalJoin(<bas_mat : j in [1..Order(H)-1]>);
      
      Anew`axes[i]`even[evens diff {1}] +:= sub<Wnew | newvects>;
      
      */
      // We do the w*h-w trick
      H := A`axes[i]`stab;
      
      // precompute the images of all the basis vectors in the basis of bas
      // We don't want to use GModuleAction

      basWmod_mat := Matrix(bas)*W_to_Wmod;
      basWmod := ChangeUniverse(RowSequence(basWmod_mat), A`Wmod);
      images := [ basWmod*h : h in H | h ne H!1];
      
      // now join these together and push to W
      images := Matrix([ Vector(w) : w in images[i], i in [1..#images]])*basWmod_mat^-1;
      
      images := [ RowSubmatrix(images, [(j-1)*#bas+1..j*#bas]) : j in [1..Order(H)-1]];

      // All the vectors from W_even have already had the w*h-w trick imposed, so don't need to do these.  We only need to do those given by even_pairs.

      // If w^h = w^g for some h and g, we only need to take one.  Also, since multipication is commutative, we may take any order on the pair which give w.

      function CommonRows(t)
        return Setseq({Sort([L[t[1]], L[t[2]]]) : L in images });
      end function;

      // We build all pairs and sort them so that they are in blocks with common 1st vector.
      image_pairs := [ CommonRows(t) : t in even_pairs ];
      lens := [#S : S in image_pairs];

      image_pairs := &cat image_pairs;
      Sort(~image_pairs, func<x,y| x[1] eq y[1] select 0 else x[1] lt y[1] select 1 else -1>, ~perm);

      // We maintain the order on the w's
      ws := &cat [ [ basmult[t[1],t[2]] where t := even_pairs[k] : j in [1..lens[k]]] : k in [1..#even_pairs]];
      ws := [ws[i^perm] : i in [1..#ws]];
      
      vprintf ParAxlAlg, 4: "    There are %o pairs to process.\n", #ws;
      
      if #ws lt 10000 then
        // We just do the easy thing
        whs := [ &+[ L[1,j]*L[2,k]*basmult[j, k] : j in Support(L[1]), k in Support(L[2]) ] : L in image_pairs];
      else
        // We take blocks of all the same first vector and use matrix multiplication
        // This is slower for small numbers but quicker for more.
        // Slower for 8000 pairs (S_6 dim 151), but quicker for 47000 pairs (S_6 dim 9797)

        whs := [];
        start := 1;
        time while exists(last){j-1 : j in [start..#image_pairs] | image_pairs[start,1] ne image_pairs[j,1]} do
          whs cat:= Flat(BulkMultiply(basmult, [image_pairs[start,1]],
                    [image_pairs[j,2] : j in [start..last]]));
          start := last + 1;
        end while;
        whs cat:= Flat(BulkMultiply(basmult, [image_pairs[start,1]],
                    [image_pairs[j,2] : j in [start..#image_pairs]]));
      end if;
      
      Anew`axes[i]`even[evens diff {1}] +:= sub<Wnew | [ whs[j]-ws[j] : j in [1..#ws]]>;
    end if;
  end for;
  vprintf ParAxlAlg, 4: "  Time taken for the odd and even parts %o.\n", Cputime(tt);

  // We update the subalgs
  vprint ParAxlAlg, 2: "  Updating the subalgebras.";
  tt := Cputime();
  subalgs := New(SubAlg);
  subalgs`subsps := [* *];
  subalgs`maps := [* *];
  subalgs`algs := A`subalgs`algs;
  for i in [1..#A`subalgs`subsps] do
    subsp := A`subalgs`subsps[i];
    map, homg, pos := Explode(A`subalgs`maps[i]);
    alg := A`subalgs`algs[pos];
    
    subspV := subsp meet V;
    bas := ExtendBasis(subspV, subsp);
    basV := bas[1..Dimension(subspV)];
    basC := bas[Dimension(subspV)+1..Dimension(subsp)];
    
    // We also calculate their images in Wnew
    basnew := FastMatrix(bas, WtoWnew_mat);
    basnewV := basnew[1..Dimension(subspV)];
    basnewC := basnew[Dimension(subspV)+1..Dimension(subsp)];
    
    vprint ParAxlAlg, 4: "  Calculating products";
    prodsVC := BulkMultiply(Anew, basnewV, basnewC);
    prodsC2 := BulkMultiply(Anew, basnewC);

    vprint ParAxlAlg, 4: "  Updating subspaces and maps";    
    newsubsp := subsp@WtoWnew + sub< Wnew | &cat prodsVC cat prodsC2>;
    
    newmap := hom<newsubsp -> alg`W | [<basnew[i], bas[i]@map> : i in [1..#bas]]
         cat [ <prodsVC[k,l], (alg!basV[k]@map * alg!basC[l]@map)`elt>
                 : k in [1..#basV], l in [1..#basC]]
         cat [ <prodsC2[l*(l-1) div 2 + k], (alg!basC[k]@map * alg!basC[l]@map)`elt>
                 : k in [1..l], l in [1..#basC]]>;
    
    H := Domain(homg);
    ReduceGenerators(~H);
    assert2 forall(err){ <v,g> : v in Basis(newsubsp), g in Generators(H) |
               ((Anew!v)*g)`elt@newmap eq ((alg!(v@newmap))*(g@homg))`elt};
    
    assert2 forall(err){<v,w> : v,w in Basis(newsubsp meet Anew`V) | ((Anew!v)*(Anew!w))`elt@newmap eq (alg!(v@newmap)*alg!(w@newmap))`elt};
    
    Append(~subalgs`subsps, newsubsp);
    Append(~subalgs`maps, <newmap, homg, pos>);
  end for;
  Anew`subalgs := subalgs;
  
  PullbackEigenvaluesAndRelations(A, ~Anew);
  vprintf ParAxlAlg, 4: "  Time taken for updating the subalgebras %o\n", Cputime(tt);

  // We also collect some relations coming from the eigenvectors
  vprint ParAxlAlg, 2: "  Collecting any new eigenvalue relations.";
  tt := Cputime();
  Anew := ImposeEigenvalues(Anew: implement := false);
  vprintf ParAxlAlg, 4: "Time taken %o.\n", Cputime(tt);

  if implement then
    vprintf ParAxlAlg, 4: "Total time taken for ExpandSpace (before ImplementRelations) %o\n", Cputime(t);
    Anew, psi := ImplementRelations(Anew);
    vprintf ParAxlAlg, 4: "Total time taken for ExpandSpace (including ImplementRelations) %o\n", Cputime(t);
    return Anew, WtoWnew*psi;
  else
    vprintf ParAxlAlg, 4: "Total time taken for ExpandSpace %o\n", Cputime(t);
    return Anew, WtoWnew;
  end if;
end intrinsic;
//
// ============== FIND EIGENVALUES AND RELATIONS ==================
//
/*

This is an internal function to impose the eigenvalue condition.

NB add Timesable

*/
intrinsic ImposeEigenvalues(A::ParAxlAlg: implement:=true) -> ParAxlAlg
  {
  This imposes the relation u*a - lambda u, for all u in U, where U is the eigenspace associated to lambda and a is an axis.
  }
  W := A`W;
  V := A`V;

  Ggr, gr := Grading(A`fusion_table); 
  require Order(Ggr) in {1,2}: "The fusion table is not Z_2-graded.";
  
  evens := {@ lambda : lambda in A`fusion_table`eigenvalues | lambda@gr eq Ggr!1 @};
  odds := {@ lambda : lambda in A`fusion_table`eigenvalues | lambda@gr eq Ggr.1 @};
  lambdas := evens join odds;

  newrels := {@ W| @};
  for i in [1..#A`axes] do
    // It is cheaper to do all multiplications in one go and then sort out afterwards
    eigsps := [ Basis(A`axes[i]`even[{@lambda@}] meet V) : lambda in evens]
           cat [ Basis(A`axes[i]`odd[{@lambda@}] meet V) : lambda in odds];
    dims := [#sp : sp in eigsps];
    eigsps := &cat eigsps;
    
    mults := BulkMultiply(A, [A`axes[i]`id`elt], eigsps)[1];
  
    newrels join:= {@ W | w  : s in [(&+dims[1..j-1]+1)..&+dims[1..j]], j in [1..#lambdas] |
             not IsZero(w) where w := mults[s] - lambdas[j]*eigsps[s] @};
  end for;
  
  rels_sub := sub<A`W | A`rels>;
  newrels_sub := sub<A`W | newrels>;
  int := newrels_sub meet rels_sub;
  bas := ExtendBasis(int, newrels_sub);
  U := GInvariantSubspace(A, bas[Dimension(int)+1..#bas]);

  A`rels join:= {@ W| w : w in Basis(U)@};

  if implement then
    return ImplementRelations(A);
  else
    return A;
  end if;
end intrinsic;
/*
intrinsic ImposeEigenvalue(A::ParAxlAlg, i::RngIntElt, lambda::.: implement:=true) -> ParAxlAlg
  {
  Let id be the ith idempotent in W and lambda an eigenvalue.  This imposes the relation u*e - lambda u, for all u in U, where U is the eigenspace associated to lambda.
  }
  W := A`W;
  V := A`V;
  id := A`axes[i]`id;
  if {@ lambda @} in Keys(A`axes[i]`odd) then
    U := A`axes[i]`odd[{@ lambda @}];
  elif {@ lambda @} in Keys(A`axes[i]`even) then
    U := A`axes[i]`even[{@ lambda @}];
  else
    error "The given eigenvalue is not valid.";
  end if;
  
  newrels := {@ W| w : u in Basis(V meet U) | w ne W!0 where w := (id*A!u)`elt - lambda*u @};

  rels_sub := sub<A`W | A`rels>;
  newrels_sub := sub<A`W | newrels>;
  int := newrels_sub meet rels_sub;
  bas := ExtendBasis(int, newrels_sub);
  U := GInvariantSubspace(A`Wmod, A`W, bas[Dimension(int)+1..#bas]);

  A`rels join:= {@ W| w : w in Basis(U)@};

  if implement then
    return ImplementRelations(A);
  else
    return A;
  end if;
end intrinsic;
*/
/*

This just finds the odd and even parts acording to the grading.

*/
intrinsic ForceGrading(A::ParAxlAlg) -> ParAxlAlg
  {
  Let inv be a Miyamoto involution corresponding to an idempotent e.  The action of inv on W has two eigenspaces, positive and negative, which gives the grading of the action of the idempotent e.  For each idempotent e, we find the grading and store these.
  }
  actionhom := GModuleAction(A`Wmod);
  for i in [1..#A`axes] do
    inv := A`axes[i]`inv;
    inv_mat := A`W_to_Wmod*(inv @ actionhom)*A`W_to_Wmod^-1;

    A`axes[i]`odd[&join Keys(A`axes[i]`odd)] := Eigenspace(inv_mat, -1);
    A`axes[i]`even[&join Keys(A`axes[i]`even)] := Eigenspace(inv_mat, 1);
  end for;
  return A;
end intrinsic;
/*

We expand the even part.

*/
//              ======================================
//
// We list some internal functions which we will use to reduce the even part
//
//              ======================================
intrinsic MultiplyDown(A::ParAxlAlg, keys::SeqEnum, i::RngIntElt: previous := AssociativeArray([* <k,-1> : k in keys*])) -> ParAxlAlg
  {
  Let A_S denote the sum of eigenspaces. For lambda in S the elements id*u - lambda*u are all in A_\{S - lambda\}, where id is the idempotent.
  
  Option argument of previous which is an Assoc of dimensions of the eigenspaces.  We only perform the operation on a eigenspace when it has a different dimension to the one listed in previous.
  }
  t := Cputime();
  orig := CheckEigenspaceDimensions(A: empty := true);
  vprint ParAxlAlg, 2: "  Multiplying down using eigenvalues.";
    
  V := A`V;
  id := Coordinates(V, A`axes[i]`id`elt);
  id_mat := &+[ Matrix( [id[i]*A`mult[j,i] : j in [1..Dimension(V)]]) : i in [1..Dimension(V)] | id[i] ne 0];
  
  for k in Reverse(keys) do
    // check whether this is different from previous and if not, then skip
    if Dimension(A`axes[i]`even[k]) eq previous[k] then
      continue k;
    end if;
    
    U := A`axes[i]`even[k] meet A`V;
    basU := Basis(U);
    for lambda in k do
      prods := FastMatrix([ Coordinates(V,u) : u in basU], id_mat);
      A`axes[i]`even[k diff {@ lambda @}] +:= 
           sub<A`W | {@ w : j in [1..Dimension(U)] | w ne A`W!0 
                      where w := prods[j] - lambda*basU[j] @}>;
    end for;
  end for;
  vprintf ParAxlAlg, 4: "  Time taken %o\n", Cputime(t);
  vprintf ParAxlAlg, 3: "Dimension of subspaces before and after are \n     %o\n and %o. \n", orig[i], CheckEigenspaceDimensions(A: empty := true)[i];
  return A;
end intrinsic;

intrinsic SumUpwards(A::ParAxlAlg, keys::SeqEnum, i::RngIntElt: previous := AssociativeArray([* <k,-1> : k in keys*])) -> ParAxlAlg
  {
  For the ith axis we do the following on the even subspaces
   A_\{S+T\} += A_\{S+T\} + A_S + A_T
   
  Option argument of previous which is an Assoc of dimensions of the eigenspaces.  We only perform the operation on a eigenspace when it has a different dimension to the one listed in previous.
  }
  tt := Cputime();
  orig := CheckEigenspaceDimensions(A: empty := true);

  // build a sequence of keys by key length
  len := Max([#k : k in keys]);
  keylen := [[ k : k in keys | #k eq j] : j in [0..len]];
  
  vprint ParAxlAlg, 2: "  Summing upwards.";
  for j in [2..#keylen] do
    for key in keylen[j] do
      subsps := [ A`axes[i]`even[k] : k in keylen[j-1] | k subset key
            and Dimension(A`axes[i]`even[k]) ne previous[k] ];
      if #subsps ne 0 then
        A`axes[i]`even[key] +:= &+ subsps;
      end if;
    end for;
  end for;
  
  vprintf ParAxlAlg, 4: "  Time taken %o\n", Cputime(tt);
  vprintf ParAxlAlg, 3: "Dimension of subspaces before and after are \n     %o\n and %o. \n", orig[i], CheckEigenspaceDimensions(A: empty := true)[i];
  return A;
end intrinsic;

intrinsic IntersectionDown(A::ParAxlAlg, keys::SeqEnum, i::RngIntElt: previous := AssociativeArray([* <k,-1> : k in keys*])) -> ParAxlAlg
  {
  For the ith axis we take intersections on the even subspaces:
  A_\{S \cap T\} += A_S \cap A_T
  
  Option argument of previous which is an Assoc of dimensions of the eigenspaces.  We only perform the operation on a eigenspace when it has a different dimension to the one listed in previous.
  }
  tt := Cputime();
  orig := CheckEigenspaceDimensions(A: empty := true);
      
  // build a sequence of keys by key length without the largest one
  len := Max([#k : k in keys]);
  keylen := [[ k : k in keys | #k eq j] : j in [0..len-1]];
  
  vprint ParAxlAlg, 2: "  Intersecting downwards.";
  
  for j in Reverse([1..#keylen-1]) do
    for key in keylen[j] do
      // take those intersections of subspaces which have changed dimension since previous
      ints := { {@k,l@} : k,l in &cat keylen[j+1..#keylen] | k meet l eq key
         and (Dimension(A`axes[i]`even[k]) ne previous[k]
                 or Dimension(A`axes[i]`even[l]) ne previous[l])};
      if #ints ne 0 then
        A`axes[i]`even[key] +:= &+ [ A`axes[i]`even[tup[1]] meet A`axes[i]`even[tup[2]] : tup in ints];
      end if;
    end for;
  end for;
  
  vprintf ParAxlAlg, 4: "  Time taken %o\n", Cputime(tt);
  vprintf ParAxlAlg, 3: "Dimension of subspaces before and after are \n     %o\n and %o. \n", orig[i], CheckEigenspaceDimensions(A: empty := true)[i];
  return A;
end intrinsic;

intrinsic ApplyUsefulFusionRules(A::ParAxlAlg, i::RngIntElt: previous := AssociativeArray([* <k,-1> : k in Keys(A`axes[i]`even)*])) -> ParAxlAlg
  {
  We impose the useful fusion rules to grow the subspaces for the ith axis.
  
  Option argument of previous which is an Assoc of dimensions of the eigenspaces.  We only perform the operation on a eigenspace when it has a different dimension to the one listed in previous.
  }
  tt := Cputime();
  orig := CheckEigenspaceDimensions(A: empty := true);

  vprint ParAxlAlg, 2: "  Applying useful fusion rules.";
  for tup in UsefulFusionRules(A`fusion_table) do
    // check whether this is different from previous and if not, then skip
    if Dimension(A`axes[i]`even[tup[1]]) eq previous[tup[1]] and Dimension(A`axes[i]`even[tup[2]]) eq previous[tup[2]] then
      continue tup;
    end if;

    A`axes[i]`even[tup[3]] +:= sub< A`W | &cat BulkMultiply(A, Basis(A`axes[i]`even[tup[1]] meet A`V), Basis(A`axes[i]`even[tup[2]] meet A`V))>;
  end for;
  
  vprintf ParAxlAlg, 4: "  Time taken %o\n", Cputime(tt);
  vprintf ParAxlAlg, 3: "Dimension of subspaces before and after are \n     %o\n and %o. \n", orig[i], CheckEigenspaceDimensions(A: empty := true)[i];
  return A;
end intrinsic;
/*

====================== REDUCE THE EVEN PART ============================

*/
/*

This function returns the a SeqEnum of dimensions of the subspaces for a given axis i.
We adjust by subtracting the dim of the empty subspace.

*/
StageDimensions := function(A, i)
  return CheckEigenspaceDimensions(A:empty:=true)[i];
end function;

SetPrevious := function(orderedsubsets, stage)
  
  return AssociativeArray([* < orderedsubsets[i], stage[i]> : i in [1..#stage]*]);
end function;
/*

The main even function

*/
intrinsic ExpandEven(A::ParAxlAlg: implement:=true, backtrack := false, reduction_limit := Maximum(Floor(Dimension(A)/4), 50)) -> ParAxlAlg
  {
  We repetedly apply the reduction tricks until there is no further change.  We reduce the algebra if the dimension of the space we can mod out by is at least the reduction_limit.
  }
  if Dimension(A) eq 0 then
    return A;
  end if;
  
  if backtrack then
    implement := false;
  end if;
  
  t := Cputime();
  vprint ParAxlAlg, 1: "Imposing the even relations.";
  
  keys := Setseq(Keys(A`axes[1]`even));
  Sort(~keys, func<x,y| #x-#y>);
  
  if #A`rels ne 0 then
    R := GInvariantSubspace(A, A`rels);
    for i in [1..#A`axes] do
      A`axes[i]`even[{@@}] +:= R;
    end for;
  end if;
  
  // We have an algorithm which we organise into several stages.  Higher stages are more computationally expensive than the previous stages, so we wish to do all stages on all axes until they don't change anymore before moving on to the next stage.
  // We complete a stage and then retry the previous stages to see if these will now give further progress.  We then go on to a higher stage.
  
  // We define a flag of the dimension of all subspaces after a given stage on a given axis.
  // In this way we keep track of whether there has been any change since the previous time we applied that stage and so if it is worth doing that stage again.
  len := #StageDimensions(A, 1);
  stage_flag := [[ [ -1 : k in [1..len]] : j in [1..5]] : i in [1..#A`axes]];
  
  // We define the set of ordered subsets
  Ggr, gr := Grading(A`fusion_table); 
  require Order(Ggr) in {1,2}: "The fusion table is not Z_2-graded.";
  
  evens := {@ lambda : lambda in A`fusion_table`eigenvalues | lambda@gr eq Ggr!1 @};
  odds := {@ lambda : lambda in A`fusion_table`eigenvalues | lambda@gr eq Ggr.1 @};
  orderedsubsets := Subsets(evens) join Subsets(odds: empty:=false);
  
  while true do
    // We find the lowest stage so that there is an axis which has changed since we last worked on it.
    so := exists(tup){ <i, j> : i in [1..#A`axes], j in [1..5] |
                           stage_flag[i,j] ne StageDimensions(A, i)};
    
    if so then
      // There is work to do, so we do it!
      i, stage := Explode(tup);
      
      // Check if we are backtracking and we already have an intersection with V
      // If so, then we want to skip to propogating relations and exit
      if backtrack and exists{i : i in [1..#A`axes] | Dimension(A`axes[i]`even[{}] meet A`V) ne 0} then
        // NB we do not make the subspace G-invariant.  It is quicker to pull back the intersection and do that in the previous (unexpanded) algebra.
        A`rels join:= &join{@ IndexedSet(Basis(A`axes[i]`even[{}])) : i in [1..#A`axes]@};
        return A;
      end if;        

      // We begin by multplying down
      if stage eq 1 then
        A := MultiplyDown(A, keys, i: previous:= SetPrevious(orderedsubsets, stage_flag[i,stage]));
        stage_flag[i, stage] := StageDimensions(A, i);

      // We sum up the subspaces
      elif stage eq 2 then
        A := SumUpwards(A, keys, i: previous:= SetPrevious(orderedsubsets, stage_flag[i,stage]));
        stage_flag[i, stage] := StageDimensions(A, i);
        
      // We take intersections
      elif stage eq 3 then
        A := IntersectionDown(A, keys, i: previous:= SetPrevious(orderedsubsets, stage_flag[i,stage]));
        stage_flag[i, stage] := StageDimensions(A, i);
        
      // We apply the useful fusion rules
      elif stage eq 4 then
        A := ApplyUsefulFusionRules(A, i: previous := SetPrevious(orderedsubsets, stage_flag[i,stage]));
        stage_flag[i, stage] := StageDimensions(A, i);
        
      // All the operations we apply above are H-invariant
      // So we only need to make the relations subspace G-invariant and add that on
      elif stage eq 5 then
        tt := Cputime();
        vprint ParAxlAlg, 2: "  Making the relations stabiliser-invariant and propogating.";
        orig := CheckEigenspaceDimensions(A: empty := true);
        
        // Check that it has changed
        altered_empties := {j : j in [1..#A`axes] | 
               Dimension(A`axes[j]`even[{@@}]) notin {0, stage_flag[j,stage,1]}};
        U := GInvariantSubspace(A, 
               &cat[ Basis(A`axes[j]`even[{@@}]) : j in altered_empties]);
        A`rels join:= {@ A`W | v : v in Basis(U) @};
        
        if backtrack and Dimension(U meet A`V) ne 0 then
          // we exit so that we can backtrack by pulling back the new relations to before the last expansion and modding out there.
          return A;
        end if;
        
        for j in [1..#A`axes] do
          A`axes[j]`even[{@@}] +:= U;
          stage_flag[j, stage] := StageDimensions(A, j);
        end for;
        
        vprintf ParAxlAlg, 4: "  Time taken %o\n", Cputime(tt);
        vprintf ParAxlAlg, 3: "Dimension of subspaces before and after are \n     %o\n and %o. \n", orig[i], CheckEigenspaceDimensions(A: empty := true)[i];
      end if;
    end if;
    
    // if there is no work to do, or we have found enough relations, then we mod out and check to see if we are really done.
    if not so or (implement and Dimension(A`axes[i]`even[{@@}]) ge reduction_limit) then
    
      // Find which empty eigenspaces are not G-invariant
      altered_empties := {j : j in [1..#A`axes] | 
               Dimension(A`axes[j]`even[{@@}]) notin {0, stage_flag[j, 5, 1]}};
      U := GInvariantSubspace(A, 
               &cat[ Basis(A`axes[j]`even[{@@}]) : j in altered_empties]);
      
      // All the rest are G-invariant, or 0 and so have already been added to rels
      
      A`rels join:= {@ A`W | v : v in Basis(U) @};
      
      if #A`rels ne 0 and implement then
        vprint ParAxlAlg, 2: "  Reducing the algebra";
        tt := Cputime();
        A := ImplementRelations(A);
        vprintf ParAxlAlg, 4: "  Time taken to reduce the algebra %o\n", Cputime(t);
      else
        // There are no relations to mod out by, or we have chosen not to implement them, so we must be done.
        vprintf ParAxlAlg, 1: "\nDim(A) is %o, Dim(V) is %o.\n", Dimension(A), Dimension(A`V);
        vprintf ParAxlAlg, 4: "Time taken for even routine %o\n", Cputime(t);
        return A;
      end if;
    end if;
    
    // We could be done already, so we check
    if Dimension(A) eq 0 or (Dimension(A) eq Dimension(A`V) and
      forall{i : i in [1..#A`axes] | &+[Dimension(A`axes[i]`even[k]) : k in keys | #k eq 1]
        + &+[Dimension(A`axes[i]`odd[k]) : k in Keys(A`axes[i]`odd) | #k eq 1]
            eq Dimension(A)})
          then

      vprintf ParAxlAlg, 1: "\nDim(A) is %o, Dim(V) is %o.\n", Dimension(A), Dimension(A`V);
      vprintf ParAxlAlg, 4: "Time taken for even routine %o\n", Cputime(t);
      return A;
    end if;
  end while;
end intrinsic;
