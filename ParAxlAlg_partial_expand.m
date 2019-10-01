/*

Search partial expansions for useful expansions and pull back the relations/eigenvectors

*/
intrinsic SearchPartialExpansions(A::ParAxlAlg: stabiliser_action := true) -> ParAxlAlg
  {
  Decomposes the complement of V in A using the MeatAxe.  For each indecomposible summand U, partially expand A by U, finds relations and eigenvectors in the resulting algebra and pull them back to A, if possible.
  }
  t := Cputime();
  G := Group(A);
  Wmod := A`Wmod;
  
  ip := GetInnerProduct(Wmod);
  Vmod := sub<Wmod | [Wmod | v : v in Basis(A`V)]>;
  Cmod := Complement(Wmod, Vmod: ip:=ip);

  tt := Cputime();
  vprint ParAxlAlg, 4: "Finding indecomposable summands to partially expand by.";
  mods := IndecomposableSummands(Cmod);
  vprintf ParAxlAlg, 4: "Time taken: %o\n", Cputime(tt);

  // loop over the modules in mods adding one at a time and pulling back any relations or eigenvectors

  while #mods ne 0 do
    U := mods[1];
    print U;
    Apar, phi := PartialExpandSpace(A, sub<A`W| [A`W!A`Wmod!u : u in Basis(U)]>: stabiliser_action := stabiliser_action);

    IndentPush(2);
    Apar := ExpandEven(Apar: implement := false);
    R := SaturateSubspace(Apar, sub<Apar`W|Apar`rels>);
    IndentPop(2);
    
    ImW := Image(phi);
    ImWR := R meet ImW;
    // Check to see if we have found any relations or eigenvectors
    if Dimension(ImWR) ne 0 then
      if not assigned pullback then
        vprint ParAxlAlg, 2: "Calculating pullback map.";
        pullback := Matrix([ ImW.i@@phi : i in [1..Dimension(ImW)]]);
      end if;
      Coeffs := {@ Coordinates(ImW, v) : v in Basis(ImWR)@};
      A`rels join:= FastMatrix(Coeffs, pullback);
      vprint ParAxlAlg, 2: "Found new relations.";
    end if;
    for i in [1..#Apar`axes] do
      for attr in {@ "odd", "even"@}, key in Keys(Apar`axes[i]``attr) do
        Eig := Apar`axes[i]``attr[key] meet ImW;
        if Dimension(Eig) ne Dimension(A`axes[i]``attr[key]) then
          if not assigned pullback then
            vprint ParAxlAlg, 2: "Calculating pullback map.";
            pullback := Matrix([ ImW.i@@phi : i in [1..Dimension(ImW)]]);
          end if;
          Coeffs := [ Coordinates(ImW, v) : v in Basis(Eig)];
          dim := Dimension(A`axes[i]``attr[key]);
          A`axes[i]``attr[key] +:= sub<A`W| FastMatrix(Coeffs, pullback)>;
          if Dimension(A`axes[i]``attr[key]) ne dim then
            vprintf ParAxlAlg, 2: "Found new eigenvalues for %o\n", key;
          end if;
        end if;
      end for;
    end for;
    // Currently we can only partial expand when there are no relations.  So, we must mod out by them.  FIX THIS!!
    if #A`rels ne 0 then
      Anew, quo := ImplementRelations(A);
      quomat := MapToMatrix(quo);
      // quomod := hom<A`Wmod -> Anew`Wmod | quomat>;
      // mods := [ Unew : j in [1..#mods] | Dimension(Unew) ne 0 where Unew := (mods[j])@quomod ];
      mods := [ Unew : j in [1..#mods] | Dimension(Unew) ne 0
           and not sub<Anew`W | [Anew`W!Anew`Wmod!u : u in Basis(Unew)]> subset Anew`V
           where Unew := sub<Anew`Wmod | FastMatrix([ A`Wmod!u : u in Basis(mods[j])], quomat)> ];
      A := Anew;
    end if;
    if assigned pullback then
      delete pullback;
    end if;
    Remove(~mods, 1);
  end while;

  return A;
end intrinsic;
/*

Do a partial expansion of U

*/
ijpos := function(i,j,n)
  if i le j then
    return &+[ n+1 -k : k in [0..i-1]] -n +j-i;
  else
    return &+[ n+1 -k : k in [0..j-1]] -n +i-j;
  end if;
end function;
/*

Partial expand by U

*/
intrinsic PartialExpandSpace(A::ParAxlAlg, U::ModTupFld: stabiliser_action := true) -> ParAxlAlg, Map
  {
  Given a subspace U of W, we expand A to a partial axial algebra where we include all products in U.
  }
  t := Cputime();
  G := Group(A);
  W := A`W;
  Wmod := A`Wmod;
  V := A`V;
  
  require #A`rels eq 0: "There are still relations to be modded out by";
  require not U subset (sub<W|A`rels> + V): "There is nothing to expand by.";
  
  vprintf ParAxlAlg, 1: "Partially expanding algebra from %o dimensions.\n", Dimension(A);
  tt := Cputime();
  // ensure that U is G-invariant
  U := GInvariantSubspace(Wmod, W, {@ W!u : u in Basis(U)@});
  
  ip := GetInnerProduct(Wmod);
  decompU := DecomposeVectorsWithInnerProduct(V, {@ W!u : u in Basis(U)@}: ip:=ip);
  
  //Now we may extend by the subspace X spanned by the projection to the complement
  
  X := sub<W| [t[2] : t in decompU]>;
  
  // We build the modules and maps
  Vmod := sub<Wmod | [Wmod | v : v in Basis(V)]>;
  Xmod := sub<Wmod | [Wmod | x : x in Basis(X)]>;
  
  VxXmod := TensorProduct(Vmod, Xmod);
  X2mod := SymmetricSquare(Xmod);

  Wmodnew, injs := DirectSum([X2mod, VxXmod, Wmod]);
  
  // We build the corresponding vector spaces and maps
  Wnew := RSpace(BaseRing(A), Dimension(Wmodnew));
  X := RSpaceWithBasis([ W | Wmod!(Xmod.i) : i in [1..Dimension(Xmod)]]);
  VX := V+X;
  
  // So VX is the subspace where we will know the products
  
  WtoWnew_mat := MapToMatrix(injs[3]);
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
  Anew`V := (VX)@WtoWnew;
  vprintf ParAxlAlg, 2: "Partially expanded to %o dimensions.\n", Dimension(Anew`W);
  vprintf ParAxlAlg, 4: "Time taken to build modules and vector spaces %o.\n", Cputime(tt);
  
  vprint ParAxlAlg, 2: "  Building the multiplication.";
  tt := Cputime();
  
  // We begin by defining two function which we will use to multiply quickly. We use these both in defining the multiplication of Anew and also when building the odd and even parts.
  // precompute mult matrices for VC and C2
  dimV := Dimension(V);
  dimX := Dimension(X);
  
  VxX := RSpace(BaseRing(A), Dimension(VxXmod));
  VxXmult := [ [VxX.(dimX*(i-1)+j) : j in [1..dimX]]: i in [1..dimV]];
  VxXtoWnew_mat := MapToMatrix(injs[2]);
  
  X2mult := [ [Wnew.ijpos(i,j,dimX) : j in [1..dimX]]: i in [1..dimX]];
  
  // ===== Now define two functions ======
  
  
  // Function which multiplies L with L
  function BulkMultiplyAtoAnewSym(L)
    // We precompute the decompositions
    decomp := DecomposeVectorsWithInnerProduct(V, [W | v : v in L]: ip:=ip);
    // We transform them into vectors in their natural spaces
    decompV := [ Coordinates(V,t[1]) : t in decomp ];
    decompX := [ Coordinates(X,t[2]) : t in decomp ];
    
    // precompute all the products we require
    prodsV := FastMatrix(BulkMultiply(A, decompV), WtoWnew_mat);
    
    newVxXmult := BulkMultiply(VxXmult, decompV, decompX);
    prodsVxX := FastMatrix([ newVxXmult[i,j] + newVxXmult[j,i] : j in [1..i], i in [1..#decomp]], VxXtoWnew_mat);
    
    prodsX2 := BulkMultiply(X2mult, decompX, decompX);
    
    ans := [[Wnew | ] : i in [1..#L]];

    for i in [1..#L] do
      for j in [1..i] do
        ans[i][j] := prodsV[i*(i-1) div 2 +j] + prodsVxX[i*(i-1) div 2+j] + prodsX2[i,j];
        if j ne i then
          ans[j][i] := ans[i][j];
        end if;
      end for;
    end for;
    
    return ans;
  end function;

  // function which multiplies L with M
  function BulkMultiplyAtoAnew(L, M)
    // We precompute the decompositions
    decomp := DecomposeVectorsWithInnerProduct(V, [W | v : v in L cat M]: ip:=ip);
    // We transform them into vectors in their natural spaces
    decompV := [ Coordinates(V,t[1]) : t in decomp ];
    decompX := [ Coordinates(X,t[2]) : t in decomp ];
    
    // precompute all the products we require
    prodsV := FastMatrix(&cat BulkMultiply(A, decompV[1..#L], decompV[#L+1..#L+#M]), WtoWnew_mat);
    
    prodsL_VxM_X := FastMatrix( &cat BulkMultiply(VxXmult, decompV[1..#L], decompX[#L+1..#L+#M]), VxXtoWnew_mat);
    prodsM_VxL_X := FastMatrix( &cat BulkMultiply(VxXmult, decompV[#L+1..#L+#M], decompX[1..#L]), VxXtoWnew_mat);
    
    prodsX2 := BulkMultiply(X2mult, decompX[1..#L], decompX[#L+1..#L+#M]);
    
    ans := [[Wnew | prodsV[(i-1)*#M +j] + prodsL_VxM_X[(i-1)*#M+j] + prodsM_VxL_X[(j-1)*#L +i] + prodsX2[i,j] : j in [1..#M]]: i in [1..#L]];
      
    return ans;
  end function;
  
  // ===== Return to intrinsic ======
  

  Anew`mult := BulkMultiplyAtoAnewSym(Basis(VX));
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
    bas_even := Basis(VX meet A`axes[i]`even[evens]);
    bas_odd := Basis(VX meet A`axes[i]`odd[odds]);

    // The even part is EvenxEven plus OddxOdd
    EvenxEven := BulkMultiplyAtoAnewSym(bas_even);
    OddxOdd := BulkMultiplyAtoAnewSym(bas_odd);
    
    Anew`axes[i]`even[evens] +:= sub<Wnew | &cat EvenxEven cat &cat OddxOdd>;
    // The odd part is EvenxOdd
    EvenxOdd := BulkMultiplyAtoAnew(bas_even, bas_odd);
    Anew`axes[i]`odd[odds] +:= sub<Wnew | &cat EvenxOdd>;
    
    if stabiliser_action then
      vprint ParAxlAlg, 2: "  Doing the w*h-w trick.";
      // We do the w*h-w trick
      H := A`axes[i]`stab;
      Aactionhom := GModuleAction(A`Wmod);
      
      // precompute the images of all the basis vectors
      images := [ FastMatrix(bas_even cat bas_odd,h@Aactionhom) : h in H | h ne H!1];
      
      // We now need to convert these images and find their products in Anew.
      im_even := [ [Coordinates(VX meet A`axes[i]`even[evens], v) : v in L[1..#bas_even]] : L in images];
      im_odd := [ [Coordinates(VX meet A`axes[i]`odd[odds], v) : v in L[#bas_even+1..#bas_even+#bas_odd]] : L in images];
      
      prods_even := [ BulkMultiply(EvenxEven, L, L) : L in im_even];
      prods_odd := [ BulkMultiply(OddxOdd, L, L) : L in im_odd];
      
      // Each w in Anew`even is represented by a tuple <u,v> and we have precomputed their products and also u*h, so we just run over k,j symmetrically
      vects_even := [ [ M[k,j] - EvenxEven[k,j] :j in [1..k], k in [1..#bas_even]] : M in prods_even];
      vects_odd := [ [ M[k,j] - OddxOdd[k,j] :j in [1..k], k in [1..#bas_odd]] : M in prods_odd];
      
      Anew`axes[i]`even[evens diff {1}] +:= sub<Wnew | Flat(vects_even) cat Flat(vects_odd)>;
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
  
    subspVX := subsp meet VX;
    subspV := subsp meet V;
    
    bas := ExtendBasis(subspV, subspVX);
    bas_all := ExtendBasis(subspVX, subsp);
    bas_subspV := bas[1..Dimension(subspV)];
    bas_subspX := bas[Dimension(subspV)+1..Dimension(subspVX)];
    bas_extra := bas_all[Dimension(subspVX)+1..Dimension(subsp)];
    bas := bas_subspV cat bas_subspX cat bas_extra;
    
    // We also calculate their images in Wnew
    basnew := FastMatrix(bas, WtoWnew_mat);
    basnewV := basnew[1..Dimension(subspV)];
    basnewX := basnew[Dimension(subspV)+1..Dimension(subspVX)];
    
    prodsVxX := BulkMultiply(Anew, basnewV, basnewX);
    // [[ Wnew |(Anew!v@WtoWnew * Anew!u@WtoWnew)`elt : v in bas_subspV] : u in bas_subspVX];
    prodsX2 := BulkMultiply(Anew, basnewX);
    // [[ Wnew |(Anew!bas_subspVX[k]@WtoWnew * Anew!bas_subspVX[l]@WtoWnew)`elt : k in [1..l]] : l in [1..#bas_subspVX]];
    newsubsp := subsp@WtoWnew + sub< Wnew | &cat prodsVxX cat prodsX2>;
    
    newmap := hom<newsubsp -> alg`W | [ <basnew[i], bas[i]@map> : i in [1..#bas]]
     cat [ <prodsVxX[k,l], (alg!bas_subspV[k]@map * alg!bas_subspX[l]@map)`elt>
             : k in [1..#bas_subspV], l in [1..#bas_subspX]]
     cat [ <prodsX2[l*(l-1) div 2 + k], (alg!bas_subspX[k]@map * alg!bas_subspX[l]@map)`elt>
             : k in [1..l], l in [1..#bas_subspX]]>;

//    newmap := hom<newsubsp -> alg`W | [ <u@WtoWnew, u@map> : u in Basis(subsp)]
//         cat [ <prodsVX[l,k], (alg!bas_subspV[k]@map * alg!bas_subspVX[l]@map)`elt>
//                 : k in [1..#bas_subspV], l in [1..#bas_subspVX]]
//         cat [ <prodsX2[l,k], (alg!bas_subspVX[k]@map * alg!bas_subspVX[l]@map)`elt>
//                 : k in [1..l], l in [1..#bas_subspVX]]>;
    
    Append(~subalgs`subsps, newsubsp);
    Append(~subalgs`maps, <newmap, homg, pos>);
  end for;
  Anew`subalgs := subalgs;
  
  PullbackEigenvaluesAndRelations(A, ~Anew);
  vprintf ParAxlAlg, 4: "  Time taken for updating the subalgebras %o\n", Cputime(tt);

  // We also collect some relations coming from the eigenvectors
  vprint ParAxlAlg, 2: "  Collecting any new eigenvalue relations.";
  tt := Cputime();
  Anew := ImposeEigenvalues(Anew: implement:=false);
  vprintf ParAxlAlg, 4: "Time taken %o.\n", Cputime(tt);

  vprintf ParAxlAlg, 4: "Total time taken to partial expand space (before ImplementRelations) %o\n", Cputime(t);
  Anew, psi := ImplementRelations(Anew);
  vprintf ParAxlAlg, 4: "Total time taken to partial expand space (including ImplementRelations) %o\n", Cputime(t);
  return Anew, WtoWnew*psi;
end intrinsic;
