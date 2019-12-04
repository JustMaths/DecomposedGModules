/*

Functions for loading and saving a ParAxlAlg as a json object

*/
import "ParAxlAlg.m": library_location;
/*

Code to implement a group name which will work in older versions of magma too.  

*/
intrinsic MyGroupName(G::GrpPerm) -> MonStgElt
  {
  If GroupName is defined in magma (roughly version 2.21 or above) it returns GroupName, otherwise it returns order_num, where <order, num> is given by IdentifyGroup. A hash is used in place of a colon.
  }
  // By doing IdentifyGroup and then SmallGroup, we get a canonical iso rep for G
  // Can only do for group orders up to 1024
  try
    ord, num := Explode(IdentifyGroup(G));
    GG := SmallGroup(ord, num);
  catch e
    GG := G;
  end try;

  try
    name := eval("GroupName(GG)");
    // magma/linux/something messes up directory names with colons, so need to substitute these...
    name := Join(Split(name, ":"), "#");
  catch e
  ord, num := Explode(IdentifyGroup(G));
    name := Sprintf("%o_%o", ord, num);
  end try;
  return name;
end intrinsic;
/*

Given a filename, return a sequence of the dihedral subalgebra types

*/
intrinsic ParseShape(name::MonStgElt) -> SetMulti
  {
  Given a filename, return a sequence of the dihedral subalgebra types.
  }
  type := {**};
  while #name ne 0 and name[1] in {"2","3","4","5","6"} do
    Include(~type, name[1..2]);
    name := name[3..#name];
  end while;
  return type;
end intrinsic;
/*

A function for choosing the filename

*/
intrinsic Filename(Ax::GSet, tau::Map, shape::SeqEnum: field := Rationals(), FT := MonsterFusionTable()) -> BoolElt, MonStgElt
  {
  Find the filename of the saved algebra for Ax, tau, shape if possible.
  }
  shapetype := &cat [ sh[2] : sh in shape];
  Miy := sub<Group(Ax) | Image(tau)>;
  num_axes := Join([ IntegerToString(#o) : o in Orbits(Miy, Ax)], "+");
 
  // We must check to see if the file already exists, so we know how to get the i right for different taus.  We assume that there is no other matching algebra ie that i:=1
  i := 1;
  
  // first check to see if the directory exists at all
  
  path := Sprintf("%o/%o/%m/%o/%o", library_location, FT`directory, field, MyGroupName(Miy), num_axes);
  if ExistsPath(path) then
    // we must now see if there is already an algebra with the same path with a different tau.
    algs := ls(path);
    shapes := [ ParseShape(sh) : sh in algs];
    possibles := {@ i : i in [1..#shapes] | shapes[i] eq ParseShape(shapetype) @};
    
    if #possibles ne 0 then
      so := false;
      for j in possibles do
        alg_type := GetTypePartialAxialAlgebra(Sprintf("%o/%o", path, algs[j]));
        _, alg_ax, alg_tau, alg_shape, _ := Explode(alg_type);
        
        so := IsIsomorphic(alg_ax, alg_tau, alg_shape, Ax, tau, shape);
        if so then
          return true, Sprintf("%o/%o", path, algs[j]);
        end if;
      end for;
    end if;
  end if;
  
  return false, _; 
end intrinsic;

intrinsic Filename(A::ParAxlAlg) -> MonStgElt
  {
  Returns a filename of the form
  
  library_location/fusion_table/field/MyGroupName/number_of_axes/shape_i.json
  
  or
  
  library_location/fusion_table/field/MyGroupName/number_of_axes/shape_i_partial.json
  
  if the algebra has not been fully reduced, where i is an index allowing different tau maps.
  }
  Miy := A`Miyamoto_group;
  shapetype := &cat [ sh[2] : sh in A`shape];
  num_axes := Join([ IntegerToString(#o) : o in Orbits(A`Miyamoto_group, A`GSet)], "+");
  
  // We must check to see if the file already exists, so we know how to get the i right for different taus.  We assume that there is no other matching algebra ie that i:=1
  i := 1;
  
  // The old type didn't have a directory name for the fusion table, so we check and reassign
  if not assigned A`fusion_table`directory then
    require A`fusion_table eq MonsterFusionTable(): "You are using a non-Monster fusion table.  Please manually update it to the latest version of fusion table with name and directory and try again.";
    A`fusion_table := MonsterFusionTable();
  end if;
  
  // first check to see if the directory exists at all
  
  
  path := Sprintf("%o/%o/%m/%o/%o", library_location, A`fusion_table`directory, BaseRing(A), MyGroupName(Miy), num_axes);
  if ExistsPath(path) then
    // we must now see if there is already an algebra with the same path with a different tau.
    algs := ls(path);
    shapes := [ ParseShape(sh) : sh in algs];
    possibles := {@ i : i in [1..#shapes] | shapes[i] eq ParseShape(shapetype) @};
    
    if #possibles ne 0 then
      so := false;
      for j in possibles do
        alg_type := GetTypePartialAxialAlgebra(Sprintf("%o/%o", path, algs[j]));
        _, alg_ax, alg_tau, alg_shape, _ := Explode(alg_type);
        
        so := IsIsomorphic(alg_ax, alg_tau, alg_shape, A`GSet, A`tau, A`shape);
        if so then
          shapetype := algs[j][1..#shapetype];
          i := algs[j][#shapetype+2];
          break j;
        end if;
      end for;
      if not so then
        // We must choose an i which doesn't conflict with those already there
        conflicts := {@ a : a in algs | a[1..#shapetype] eq shapetype @};
        eyes := { a[#shapetype+2] : a in conflicts };
        i := Min({1..#eyes+1} diff eyes);
      end if;
    end if;
  end if;
  
  if Dimension(A) eq Dimension(A`V) then
    return path cat Sprintf("/%o_%o.json", shapetype, i);
  else
    return path cat Sprintf("/%o_%o_partial.json", shapetype, i);
  end if;
end intrinsic;
/*

Provide some directory functions for magma

*/
ls_script := "
import os
import sys

filename = sys.argv[1]

print \"/\".join(os.listdir(filename))
";

// Added to fix weird problem with the script not running properly on some machines
// ASCI char 13 (not \r in magma!) is ignored on some computers and causes an error on others.
ls_script := &cat Split(ls_script, CodeToString(13));

intrinsic ls(dirname::MonStgElt) -> SeqEnum
  {
  ls
  }
  string := Pipe(Sprintf("python -c '%o' '%o'", ls_script, dirname), "");
  return Split(string, "\n/");
end intrinsic;

size_script := "
import os
import sys

filename = sys.argv[1]

print os.stat(filename).st_size
";

// Added to fix weird problem with the script not running properly on some machines
// ASCI char 13 (not \r in magma!) is ignored on some computers and causes an error on others.
size_script := &cat Split(size_script, CodeToString(13));

intrinsic Size(filename::MonStgElt) -> RngIntElt
  {
  Gets the file size.
  }
  string := Pipe(Sprintf("python -c '%o' '%o'", size_script, filename), "");
  return eval(string);
end intrinsic;

exists_script := "
import os
import sys

filename = sys.argv[1]

print os.path.isdir(filename)
";

// Added to fix weird problem with the script not running properly on some machines
// ASCI char 13 (not \r in magma!) is ignored on some computers and causes an error on others.
exists_script := &cat Split(exists_script, CodeToString(13));

intrinsic ExistsPath(dirname::MonStgElt) -> BoolElt
  {
  Returns whether the directory given by dirname exists.
  }
  string := Pipe(Sprintf("python -c '%o' '%o'", exists_script, dirname), "");
  if string eq "True\n" then
    return true;
  else
    return false;
  end if;
end intrinsic;
//
// =============== Code to save a ParAxlAlg ================
//
/*

Saves a partial axial algebra

*/
intrinsic SavePartialAxialAlgebra(A::ParAxlAlg: filename:=Filename(A))
  {
  Saves a partial axial algebra in JSON format.  Saves by default using the Filename function.
  }
  vprintf ParAxlAlg, 2: "Saving partial axial algebra...";
  
  // We check to see if the path exists and if not create it.
  paths := Split(filename, "/");
  path := &cat[ p cat "/" : p in paths[1..#paths-1]];
  System(Sprintf("mkdir -p '%o'", path));
  
  // To save larger algebras without hitting magma's limit on strings of 2^31bits we do each element in the list seperately
  L := [ J[2..#J-2] where J := JSON([*l*]) : l in ParAxlAlgToList(A) ];
  
  System(Sprintf("rm -fr '%o'", filename));
  maxlength := 8000;
  str := "{\n" cat L[1];
  for l in L[2..#L] do
    // we remove some stray "\n"
    ll := l[1] eq "\n" select (l[#l] eq "\n" select l[2..#l-1] else l[2..#l])
             else l[#l] eq "\n" select l[1..#l-1] else l;
    if #str + #ll lt maxlength then
      str cat:= ",\n" cat ll;
    else
      PrintFile(filename, str cat ",");
      str := ll;
    end if;
  end for;
  PrintFile(filename, str cat "\n}");
  
  vprintf ParAxlAlg, 2: " complete!\n";
end intrinsic;
/*

Code to serialise some types that will be useful

*/
intrinsic JSON(x::ParAxlAlgElt : nl:="\n", sparse_dim:=10) -> MonStgElt
  {
  Serialise a partial axial algebra element as a sequence.  Use sparse form if the degree is greater than sparse_dim.  Set sparse_dim to e negative to force non-sparse form.
  }
  return JSON(x`elt: nl:=nl, sparse_dim:=sparse_dim);
end intrinsic;

intrinsic JSON(x::ModTupRngElt : nl:="\n", sparse_dim:=10) -> MonStgElt
  {
  Serialise a vector as a sequence.  Use sparse form if the degree is greater than sparse_dim.  Set sparse_dim to e negative to force non-sparse form.

  }
  if sparse_dim ge 0 and Degree(x) gt sparse_dim then
    return JSON(SparseMatrix(x): nl:=nl);
  else
    return JSON(Eltseq(x): nl:=nl);
  end if;
end intrinsic;

intrinsic JSON(x::ModTupRng : nl:="\n", sparse_dim:=10) -> MonStgElt
  {
  Serialise a vector (sub)space as a sequence of basis elements.  Use sparse form if the degree is greater than sparse_dim.  Set sparse_dim to e negative to force non-sparse form.
  }
  if sparse_dim ge 0 and Degree(x) gt sparse_dim then
    return JSON(SparseMatrix(BasisMatrix(x)): nl:=nl);
  else
    return JSON([ Eltseq(v): v in Basis(x)]: nl:=nl);
  end if;
end intrinsic;

intrinsic JSON(x::Set : nl:="\n") -> MonStgElt
  {
  Serialise a set as a sequence.
  }
  return JSON(Setseq(x));
end intrinsic;
/*

Main code to serialise a ParAxlAlg

*/
intrinsic JSON(A::ParAxlAlg: subalgs:=0) -> MonStgElt
  {
  Serialise a partial axial algebra as a JSON object.
  
  There is an optional flag, subalgs.  If 1 then it saves all subalgebra information recursively, if 0 it only saves the subalgebras of the top algebra and if -1 it doesn't save any.  The default is 0.
  }
  return JSON(ParAxlAlgToList(A: subalgs := subalgs));
end intrinsic;


intrinsic ParAxlAlgToList(A::ParAxlAlg: subalgs:=0) -> List
  {
  Converts a partial axial algebra to a list prior to serialising as a JSON object.
  
  There is an optional flag, subalgs.  If 1 then it saves all subalgebra information recursively, if 0 it only saves the subalgebras of the top algebra and if -1 it doesn't save any.  The default is 0.
  }
  G := Group(A);
  gen := GeneratorsSequence(G);
  act := Action(G, A`GSet);
  orb_reps := {@ o[1] : o in Orbits(G, A`GSet) @};
  
  alg := [* *];
  Append(~alg, <"class", "Partial axial algebra">);

  Append(~alg, <"field", Sprintf("%m", BaseRing(A))>);
  Append(~alg, <"GSet", [* [*gen[i], gen[i]@act*] : i in [1..#gen] *]>);
  Append(~alg, <"tau", [* [* i, i@A`tau *] : i in orb_reps *]>);
  Append(~alg, <"shape", [* [* sh[1], sh[2] *] : sh in A`shape *]>);
  
  gen_mat := ActionGenerators(A`Wmod);
  assert #gen eq #gen_mat;

  if Dimension(A) gt 10 then
    gen_mat := [ SparseMatrix(M) : M in gen_mat];
  end if;
  Append(~alg, <"Wmod", [* [* gen[i], gen_mat[i] *] : i in [1..#gen] *]>);
  
  Append(~alg, <"V", A`V>);
  
  Append(~alg, <"table", FusTabToList(A`fusion_table)>);
  
  if not assigned A`mult then
    assert Dimension(A) eq 0;
    return alg;
  end if;
  
  Append(~alg, <"GSet_to_axes", [* [* Position(Image(A`GSet_to_axes), A`axes[i]`id`elt), i *] : i in [1..#A`axes] *]>);
  
  mult := [SparseMatrix(Matrix(A`mult[i])) : i in [1..#A`mult]];
  Append(~alg, <"mult", A`mult>);
  
  axes := [];
  for i in [1..#A`axes] do
    axes[i] := AssociativeArray();
    axes[i]["id"] := A`axes[i]`id;
    axes[i]["stab"] := GeneratorsSequence(A`axes[i]`stab);
    axes[i]["inv"] := A`axes[i]`inv;
    axes[i]["even"] := A`axes[i]`even;
    axes[i]["odd"] := A`axes[i]`odd;
  end for;
  Append(~alg, <"axes", axes>);

  if assigned A`subalgs and subalgs ge 0 then
    Append(~alg, <"subalgs", SubAlgToList(A`subalgs :subalgs:= subalgs eq 1 select 1 else subalgs-1)>);
  end if;
  
  if assigned A`rels then
    Append(~alg, <"rels", Setseq(A`rels)>);
  end if;
  return alg;
end intrinsic;
/*

Code to serialise a subalgebra

*/
intrinsic SubAlgToList(x::SubAlg: subalgs := -1) -> List
  {
  Transform a Subalgebra to a List prior to serialising as a JSON.
  }
  alg := [* *];

  Append(~alg, <"subsps", x`subsps>);
  
  maps := [];
  for i in [1..#x`maps] do
    map, homg, pos := Explode(x`maps[i]);
    maps[i] := [* [* [* x, x@map *] : x in Basis(Domain(map))*],
                        [* [*x, x@homg *] : x in Generators(Domain(homg))*],
                        pos*];
  end for;
  Append(~alg, <"maps", maps>);

  Append(~alg, <"algs", [ParAxlAlgToList(alg: subalgs:=subalgs) : alg in x`algs]>);

  return alg;
end intrinsic;
//
// =============== Code to load a ParAxlAlg ================
//
/*

A useful intrinsic to load in a saved subspace

*/
intrinsic Subspace(W::ModTupRng, L::List) -> ModTupRng
  {
  Load a subspace stored in List form.
  }
  return sub<W | [ W | Numbers(v): v in L]>;
end intrinsic;

intrinsic Subspace(W::ModTupRng, S::Assoc) -> ModTupRng
  {
  Load a subspace stored in sparse matrix form.
  }
  return RowSpace(SparseMatrix(BaseRing(W), S));
end intrinsic;
/*

Loads just enough of the file to get the shape info

*/
intrinsic GetTypePartialAxialAlgebra(filename::MonStgElt) -> Tup
  {
  Partially load the axial algebra given by filename and return a tuple of the field, GSet, tau-map and shape and dim (or -1 if no dimension is found).
  }
  vprint ParAxlAlg, 2: "Partially Loading partial axial algebra...";
  paths := Split(filename, "/");
  if "." notin paths[#paths] then
    realfilename := filename cat ".json";
  else
    realfilename := filename;
  end if;

  // If the file is small, then we assume it is for an algebra of dimension 0 and open it all.  Otherwise, we just open a the first few lines
  if Size(filename) le 3000 then
    A := LoadPartialAxialAlgebra(filename);
    return <BaseRing(A), A`GSet, A`tau, A`shape, Dimension(A)>;
  end if;

  file := Open(filename, "r");
  text := "";
  line := "";
  // We wish to read everything up to GSet_to_axes
  while "Wmod" notin line do
    line := Gets(file);
    text cat:= line;
  end while;
  delete file;
  
  pos := Position(text, "Wmod");
  assert exists(i){ i : i in Reverse([1..#text]) | i le pos and text[i] eq ","};
  text := text[1..i-1] cat "}";
  
  alg := ParseJSON(text);
  keys := Keys(alg);
  require "class" in keys and alg["class"] eq "Partial axial algebra": "The file given does not encode a partial axial algebra.";
  require keys eq {"class", "field", "GSet", "tau", "shape"}: "The file doesn't contain the shape information in the top part";
  
  F := eval(alg["field"]);
  gens := [Numbers(k[1]) : k in alg["GSet"]];
  images := [Numbers(k[2]) : k in alg["GSet"]];
  n := Max(gens[1]);
  G := PermutationGroup<n | gens>;
  m := Max(images[1]);
  act := hom<G -> Sym(m) | [<G!gens[i], Sym(m)!images[i]> : i in [1..#gens]]>;
  
  Ax := IndexedSet([1..m]);
  AxxG := CartesianProduct(Ax, G);
  f := map<AxxG -> Ax | y:-> y[1]^(y[2]@act)>;
  Ax := GSet(G, Ax, f);
  
  images := [];
  for k in alg["tau"] do
    o := Orbit(G, Ax, k[1]);
    gs := [ g where _,g := IsConjugate(G, Ax, k[1], i) : i in o];
    images cat:= [<o[i],(G!Numbers(k[2]))^gs[i]> : i in [1..#o]];
  end for;
  
  tau := map<Ax->G | images>;
  
  shape := [ < {@ i : i in Numbers(sh[1])@}, sh[2]> : sh in alg["shape"] ];
  
  return <F, Ax, tau, shape, -1>;  
end intrinsic;
/*

Load

*/
intrinsic LoadPartialAxialAlgebra(filename::MonStgElt) -> ParAxlAlg
  {
  Loads a partial axial algebra from the location given.
  }
  vprintf ParAxlAlg, 2: "Loading partial axial algebra...";
  paths := Split(filename, "/");
  if "." notin paths[#paths] then
    realfilename := filename cat ".json";
  else
    realfilename := filename;
  end if;
  
  string := Read(realfilename);
  // remove any end of line characters that magma tends to add
  string := &cat Split(string, "\\\n");
  alg := ParseJSON(string);
  vprintf ParAxlAlg, 2: " complete!\n";
  return PartialAxialAlgebra(alg);
end intrinsic;

intrinsic PartialAxialAlgebra(alg::Assoc) -> ParAxlAlg
  {
  Creates a partial axial algebra A from an associative array.  We assume that the associative array represents A stored in json format.
  }
  keys := Keys(alg);
  require "class" in keys and alg["class"] eq "Partial axial algebra": "The file given does not encode a partial axial algebra.";
  
  A := New(ParAxlAlg);
  
  F := eval(alg["field"]);
  gens := [Numbers(k[1]) : k in alg["GSet"]];
  images := [Numbers(k[2]) : k in alg["GSet"]];
  n := Max(gens[1]);
  G := PermutationGroup<n | gens>;
  A`group := G;
  m := Max(images[1]);
  act := hom<G -> Sym(m) | [<G!gens[i], Sym(m)!images[i]> : i in [1..#gens]]>;
  
  Ax := IndexedSet([1..m]);
  AxxG := CartesianProduct(Ax, G);
  f := map<AxxG -> Ax | y:-> y[1]^(y[2]@act)>;
  Ax := GSet(G, Ax, f);
  A`GSet := Ax;
  
  images := [];
  for k in alg["tau"] do
    o := Orbit(G, Ax, k[1]);
    gs := [ g where _,g := IsConjugate(G, Ax, k[1], i) : i in o];
    images cat:= [<o[i], (G!Numbers(k[2]))^gs[i]> : i in [1..#o]];
  end for;
  
  A`tau := map<Ax->G | images>;
  Miy := sub<G | Image(A`tau)>;
  A`Miyamoto_group := Miy;
  
  A`shape := [ < {@ i : i in Numbers(sh[1])@}, sh[2]> : sh in alg["shape"] ];

  A`number_of_axes := #Ax;

  mats := [ Matrix(F, alg["Wmod"][i,2]) : i in [1..#gens]];
  A`Wmod := GModule(G, MatrixAlgebra<F, Nrows(mats[1]) | mats >);

  A`W := RSpace(F, Dimension(A`Wmod));
  A`V := Subspace(A`W, alg["V"]);

  A`fusion_table := FusionTable(alg["table"]);

  if "mult" notin keys then
    assert Dimension(A) eq 0;
    A`GSet_to_axes := map<Ax -> A`W | i :-> A`W!0>;
    return A;
  end if;
  
  if #alg["mult"] eq 0 then
    // We are loading an algebra with no multiplication yet known
    A`mult := [];
  elif Type(alg["mult"][1]) eq Assoc then
    A`mult := [ Rows(Matrix(SparseMatrix(F, S))) : S in alg["mult"]];
  else
    A`mult := [ [ A`W!Numbers(row): row in mat ]: mat in alg["mult"]];
  end if;

  if "subalgs" in keys then
    subalgs := New(SubAlg);
    subalgs`subsps := [* Subspace(A`W, bas) : bas in alg["subalgs"]["subsps"] *];
    subalgs`algs := {@ PartialAxialAlgebra(x) : x in alg["subalgs"]["algs"] @};
    
    subalgs`maps := [* *];
    for i in [1..#alg["subalgs"]["maps"]] do
      map_list, homg_list, pos := Explode(alg["subalgs"]["maps"][i]);
      map := hom<subalgs`subsps[i] -> subalgs`algs[pos]`W | [ <Numbers(t[1]), Numbers(t[2])> : t in map_list]>;
      
      H := sub<G | [G!Numbers(t[1]) : t in homg_list]>;
      homg := hom< H -> Group(subalgs`algs[pos]) | [ <Numbers(t[1]), Numbers(t[2])> : t in homg_list]>;
      Append(~subalgs`maps, <map, homg, pos>);
    end for;
    A`subalgs := subalgs;
  end if;
  
  A`axes := [];
  for i in [1..#alg["axes"]] do
    idem := New(AxlAxis);
    idem`id := A!Numbers(alg["axes"][i]["id"]);
    idem`stab := sub<G | [G| G!Numbers(x) : x in alg["axes"][i]["stab"]]>;
    idem`inv := G!Numbers(alg["axes"][i]["inv"]);
    
    idem`even := AssociativeArray();
    for k in Keys(alg["axes"][i]["even"]) do
      idem`even[eval(k)] := Subspace(A`W, alg["axes"][i]["even"][k]);
    end for;

    idem `odd := AssociativeArray();    
    for k in Keys(alg["axes"][i]["odd"]) do
      idem`odd[eval(k)] := Subspace(A`W, alg["axes"][i]["odd"][k]);
    end for;
    Append(~A`axes, idem);
  end for;
  
  // We provide a function from the GSet to W
  images := [];
  for pair in alg["GSet_to_axes"] do
    i, j := Explode(pair);
    o := Orbit(G, Ax, i);
    gs := [ g where _, g := IsConjugate(G, Ax, i, k) : k in o];
    images cat:= [ < o[k], (A`axes[j]`id*gs[k])`elt> : k in [1..#o]];
  end for;
  A`GSet_to_axes := map<Ax -> A`W | images>;  
  
  if "rels" in keys then
    A`rels := {@ A`W | A`W!Numbers(v) : v in alg["rels"] @};
  end if;
  
  return A;
end intrinsic;
/*

Loads all axial algebras with a given group

*/
intrinsic LoadAllGroup(G::GrpPerm :field := Rationals(), FT:= MonsterFusionTable(), library := library_location, partial:=false) -> SeqEnum
  {
  Returns all partial axial algebras with group G.
  }
  return LoadAllGroup(MyGroupName(G): field := field, FT:= FT, library:=library, partial:=partial);
end intrinsic;

intrinsic LoadAllGroup(grp_name::MonStgElt :field := Rationals(), FT:= MonsterFusionTable(), library := library_location, partial:=false) -> SeqEnum
  {
  Returns all partial axial algebras with groupname grp_name.
  }
  // magma/linux/something screws up directorynames with colons, so we sustitute
  grp_name := Join(Split(grp_name, ":"), "#");
  path := Sprintf("%o/%o/%m/%o", library, FT`directory, field, grp_name);
  if not ExistsPath(path) then
    return [];
  end if;
  L := [];
  for num in Sort(ls(path)) do
    shapes := Sort(ls(Sprintf("%o/%o", path, num)));
    for filename in shapes do
      if partial or "_partial" notin filename then
        Append(~L, LoadPartialAxialAlgebra(Sprintf("%o/%o/%o", path, num, filename)));
      end if;
    end for;
  end for;
  
  return L;
end intrinsic;
