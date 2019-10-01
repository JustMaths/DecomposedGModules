/*

Some functions for checking properties of partial axial algebras

*/
// Sorts algebras by GroupName, axes and shape
function PrintSort(X,Y)
  x := [GroupName(MiyamotoGroup(X)), Join([ Sprintf("%o", #o) : o in Orbits(MiyamotoGroup(X), X`GSet)], "+"), &cat[sh[2] : sh in X`shape]];
  y := [GroupName(MiyamotoGroup(Y)), Join([ Sprintf("%o", #o) : o in Orbits(MiyamotoGroup(Y), Y`GSet)], "+"), &cat[sh[2] : sh in Y`shape]];
  if x[1] lt y[1] then
    return -1;
  elif x[1] gt y[1] then
    return 1;
  else
    if x[2] lt y[2] then
      return -1;
    elif x[2] gt y[2] then
      return 1;
    else
      if x[3] lt y[3] then
        return -1;
      elif x[3] gt y[3] then
        return 1;
      else
        return 0;
      end if;
    end if;
  end if;
end function;

intrinsic PrintProperties(algs::SeqEnum, filename::MonStgElt: long := false, header := true, no_6A5A:=true, shortshape:=true, zerodim:=true)
  {
  Prints in latex format to the filename the properties of the algebras in algs.  Short version is G, axes, shape, dim, m, form.  Long adds primitive, 2Ab, 3A, 4A, 5A.  zerodim toggles if the 0-dimensional algebras are printed. shortshape writes the shape with multiplicites and no_6A5A supresses printing 6A or 5A algebras.
  }
  its := func< x | IntegerToString(x)>;
  BoolToYN := func< v | v select "yes" else "no">;

  Sort(~algs, PrintSort);
  str := [];
  for i in [1..#algs] do
    A := algs[i];
    
    // If not zerodim then we don't print the 0-dim algebras
    if not zerodim and Dimension(A) eq 0 then
      continue;
    end if;
    
    num_axes := Join([ Sprintf("%o", #o) : o in Orbits(MiyamotoGroup(A), A`GSet)], "+");
    
    if shortshape then
      shape_mults := {* sh[2] : sh in A`shape *};
      shape_set := {@ sh[2] : sh in A`shape @};

      // Realy we want to remove the 4Bs in the same orbit as the 6As too, but this is too much work...
      if no_6A5A and shape_set diff {@ "6A", "5A" @} ne {@@} then
        // if you try to use diff, it reorders!
        shape_set := {@ sh : sh in shape_set | sh notin {"6A", "5A"} @};
      end if;
      shapetype := "$" cat Join([ (mult gt 1 select "(" else "") cat sh cat 
                                  (mult gt 1 select Sprintf(")^{%o}", mult) else "") 
                             where mult := Multiplicity(shape_mults, sh) : sh in shape_set], " \\, ") cat "$";
    else
      shapetype := "$" cat &cat [ sh[2] : sh in A`shape] cat "$";
    end if;

    line := [ "$" cat GroupName(MiyamotoGroup(A):TeX:=true) cat "$", num_axes, shapetype ];
    if Dimension(A) eq 0 then
      line cat:= [its(Dimension(A)), "0", "-"];
    elif Dimension(A) ne Dimension(A`V) then
      line cat:= [ "?", "", ""];
    else
      prop := Properties(A);
      line cat:= [ its(Dimension(A)), its(prop[5]), prop[3] select "pos" else prop[4] select "semi" else "no"];
    end if;
    
    if long then
      if Dimension(A) eq 0 then
        line cat:= [ "-" : j in [1..5]];
      elif Dimension(A) ne Dimension(A`V) then
        line cat:= [ "" : j in [1..5]];
      else
        // primitive
        line cat:= [ BoolToYN(prop[1]) ];
        conds := prop[6];
        for cond in ["2Ab", "3A", "4A", "5A"] do
          so := exists(j){ j : j in [1..#conds] | conds[j,1] eq cond};
          
          line cat:= [ so select BoolToYN(conds[j,2]) else "-" ];
        end for;
      end if;
    end if;
    
    Append(~str, line);
  end for;
  
  if #str ne 0 then
    text := Join([ Join(line, " & ") : line in str], "\\\\\n");
  else
    text := "";
  end if;
  
  if header then
    if not long then
      text := "\\begin{longtable}{cccccc}\n$G$ & axes & shape & dim & $m$ & form\\\\\n\\hline\n" cat text cat "\n\\hline\n\\end{longtable}";
    else
      text := "\\begin{longtable}{ccccccccccc}\n$G$ & axes & shape & dim & $m$ & form & primitive & 2Ab & 3A & 4A & 5A \\\\\n\\hline\n" 
         cat text cat "\\\\\n\\hline\n\\end{longtable}";
    end if;
  end if;
  
  Write(filename, text);
end intrinsic;

intrinsic CheckAllGroup(grp_name::MonStgElt) -> List
  {
  Checks all algebras with that group.
  }
  // magma/linux/something screws up directorynames with colons, so we substitute
  grp_name := Join(Split(grp_name, ":"), "#");
  algs := LoadAllGroup(grp_name);
  
  props := [Properties(A) : A in algs];
  
  for p in [1..#props] do
    if props[p] eq [* *] then
      continue;
    end if;
    if not props[p,1] then
      printf "%o is non-primitive.\n", algs[p];
    end if;
    if not props[p,2] then
      printf "%o has no form.\n", algs[p];
    elif not props[p,3] and props[p,4] then
      printf "%o has a form; it is positive semidefinite but not positive definite.\n", algs[p];
    elif not props[p,3] and not props[p,4] then
      printf "%o has a form but it is not positive semidefinite.\n", algs[p];
    end if;
    for i in [1..#props[p,6]] do
      if not props[p,6,i,2] then
        printf "%o has failed the %o condition.\n", algs[p], props[p,6,i,1];
      end if;
    end for;
  end for;

  try
    max := Maximum({ props[p,5] : p in [1..#props] | props[p] ne [* *]});
    printf "The maximum m found was %o for the algebras %o.\n", max, 
      { algs[p] : p in [1..#props] | props[p] ne [* *] and props[p,5] eq max};
  catch e;
    print "There are no non-zero algebras.";
  end try;

  return props;
end intrinsic;

intrinsic CheckAllGroup(G::GrpPerm) -> List
  {
  Checks all algebras with that group.
  }
  return CheckAllGroup(MyGroupName(G));
end intrinsic;

intrinsic Properties(A::ParAxlAlg) -> List
  {
  Returns a list with the following properties:
  
  - if it is primitive
  - whether a form exists
  - whether it is positive definite
  - whether it is positive semidefinite
  - mimimal m for which A is m-closed
  - whether the 2Ab, 3A, 4A, 5A conditions hold
  }
  if Dimension(A) eq 0 then
    return [* *];
  end if;
  prim := forall{ r : r in CheckEigenspaceDimensions(A) | r[1] eq 1};
  so, F, m := HasFrobeniusForm(A);
  
  if so then
    try
      pos := IsPositiveDefinite(F);
      if not pos then
        semipos := IsPositiveSemiDefinite(F);
      else
        semipos := pos;
      end if;
    catch e
      pos := false;
      semipos := false;
    end try;
  else
    pos := so;
    semipos := pos;
  end if;

  L := CheckSubalgebraConditions(A);
  
  return [* prim, so, pos, semipos, m , L *];
end intrinsic;

intrinsic CheckSubalgebraConditions(A::ParAxlAlg) -> List
  {
  Checks the 2Ab, 3A, 4A, 5A conditions, returns a sequence of boolean and a certificate if false.
  }
  if Dimension(A) eq 0 then
    return [* *];
  end if;
  Ax := A`GSet;
  tau := A`tau;
  shape := A`shape;
  G := MiyamotoGroup(A);
  Ax_to_axes := A`GSet_to_axes;
  
  out := [* *];
  
  function CheckCondition(algs, object, extrabasis)
    orbs :=  &join {@ Orbit(G, Ax, ax) : ax in algs @};
    
    // check whether the object being the same implies the extra basis vector is the same
    so := false;
    for ax in algs do
      obj := object(ax);
      x := extrabasis(ax);
      
      others := {@ t : t in orbs | t ne ax and object(t) eq obj @};
      so := exists(cert){ p : p in others | extrabasis(p) ne x};
      if so then
        return [* false, <ax, cert> *];
      end if;
    end for;
    return [* true *];  
  end function;
  
  function rho(X)
    return sub<G | X[1]@tau*X[2]@tau>;
  end function;
  
  // Find all 2A algebras
  if exists{sh : sh in shape | sh[2] in {"2A", "4B", "6A"} } then
    algs := {@ sh[1] : sh in shape | sh[2] eq "2A" @} join
              &join {@ {@ {@ sh[1,1], sh[1,3] @}, {@ sh[1,2], sh[1,4] @} @} : sh in shape | sh[2] eq "4B" @}
              join {@ {@ sh[1,1], sh[1,4] @} : sh in shape | sh[2] eq "6A" @};
    
    function extrabasis(p)
      return (8*A!p[1]@Ax_to_axes*A!p[2]@Ax_to_axes)`elt - p[1]@Ax_to_axes - p[2]@Ax_to_axes;
    end function;
    
    ans := CheckCondition(algs, rho, extrabasis);
    Append(~out, [* "2Ab" *] cat ans);
  end if;
  
  // Find all 3A algebras
  if exists{sh : sh in shape | sh[2] in {"3A", "6A"} } then
    algs := {@ sh[1] : sh in shape | sh[2] eq "3A" @} join
              &join {@ {@ {@ sh[1,1], sh[1,3], sh[1,5] @}, {@ sh[1,2], sh[1,4], sh[1,6] @} @} : sh in shape | sh[2] eq "6A" @};
    
    function extrabasis(p)
      return 2^5*(A!p[1]@Ax_to_axes*A!p[2]@Ax_to_axes)`elt - 2*p[1]@Ax_to_axes - 2*p[2]@Ax_to_axes - p[3]@Ax_to_axes;
    end function;
    
    ans := CheckCondition(algs, rho, extrabasis);
    Append(~out, [* "3A" *] cat ans);
  end if;
  
  // Find all 4A algebras
  if exists{sh : sh in shape | sh[2] eq "4A" } then
    algs := {@ sh[1] : sh in shape | sh[2] eq "4A" @};
    
    function extrabasis(p)
      return 2^6*(A!p[1]@Ax_to_axes*A!p[2]@Ax_to_axes)`elt - 3*p[1]@Ax_to_axes - 3*p[2]@Ax_to_axes - p[3]@Ax_to_axes - p[4]@Ax_to_axes;
    end function;
    
    ans := CheckCondition(algs, rho, extrabasis);
    Append(~out, [* "4A" *] cat ans);
  end if;
  
  // Find all 5A algebras
  if exists{sh : sh in shape | sh[2] eq "5A" } then
    algs := {@ sh[1] : sh in shape | sh[2] eq "5A" @};
    
    function extrabasis(p)
      x := 2^7*(A!p[1]@Ax_to_axes*A!p[2]@Ax_to_axes)`elt - 3*p[1]@Ax_to_axes - 3*p[2]@Ax_to_axes + p[3]@Ax_to_axes + p[4]@Ax_to_axes + p[5]@Ax_to_axes;
      return {-x, x};
    end function;
    
    ans := CheckCondition(algs, rho, extrabasis);
    Append(~out, [* "5A" *] cat ans);
  end if;

  return out;
end intrinsic;
