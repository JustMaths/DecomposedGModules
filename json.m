/*

Code for saving and loading magma objects to/from JSON format.
Written by Michael Fryers, 2016.
Edited by Justin McInroy 2017.

*/

ZZ := Integers();

QQ := Rationals();

map := func<f,l| [f(x):x in l] >;
indent := " ";

maxline := 200;

// Utilities

function makeseq(open, elts, sep, close, nl)
  if &and["\n" notin s : s in elts] then
  short := open cat " " cat Join(elts, sep cat " ") cat " " cat close;
    if #short le maxline then return short; end if;
  end if;
  newnl := nl cat indent;
  return open cat newnl cat Join(elts, sep cat newnl) cat nl cat close;
end function;

intrinsic AssociativeArray(x::List) -> Assoc
  {
  Convert a list of pairs into an associative array.
  }
  A := AssociativeArray();
  for p in x do
    require #p eq 2 : "Ill—formed pair in AssociativeArray";
    A[p[1]] := p[2];
  end for;
  return A;
end intrinsic;

// Generic structures

intrinsic JSON(x::Assoc : nl:="\n") -> MonStgElt
  {
  Serialise an associative array as a JSON object.
  }
  newnl := nl cat indent;

  keys := [ k : k in Keys(x)];
  try
    Sort(~keys);
  catch e;
  end try;

  strs := [ Sprintf("\"%o\": %o", k, JSON(x[k] : nl:=newnl)) : k in keys ];

  return makeseq("{", strs, ",", "}", nl);
end intrinsic;

intrinsic JSON(x::List : nl:="\n") -> MonStgElt
  {
  Serialise a list: if the first element is a pair then we take it to be <key, value> pairs and
produce a JSON object; otherwise we produce a JSON array.
  Note that an empty list is serialised as "[ ]", never as "\{ \}".
  }
  newnl := nl cat indent;
  if #x gt 0 and Type(x[1]) eq Tup and #x[1] eq 2 then
    require forall{true:t in x|Type(t) eq Tup and #t eq 2}: "Ill—formed pair—list in JSON";
    strs := [ Sprintf("\"%o\": %o", t[1], JSON(t[2] : nl:=newnl)) : t in x ];
    return makeseq("{", strs, ",", "}", nl);
  else
    return makeseq("[", [JSON(y : nl:=newnl):y in x], ",", "]", nl);
  end if;
end intrinsic;

intrinsic JSON(x::SeqEnum : nl:="\n") -> MonStgElt
  {
  Serialise a sequence in the same way as for a list.
  }
  return JSON([* e:e in x *] : nl:=nl);
end intrinsic;

// Atoms

intrinsic JSON(x::MonStgElt : nl:="\n") -> MonStgElt
  {
  Serialise a string. We cope with ASCII printables, newlines, and tabs.
  }
  y := "";
  for c in Eltseq(x) do
    if c eq "\"" or c eq "\\" then y cat:= "\\" cat c;
    elif c eq "\n" then y cat:= "\\n";
    elif c eq "\t" then y cat:= "\\t";
    else y cat:= c;
    end if;
  end for;
  return "\"" cat y cat "\"";
end intrinsic;

intrinsic JSON(x::RngIntElt : nl:="\n") -> MonStgElt
  {
  Serialise an integer.
  }
  return IntegerToString(x);
end intrinsic;

intrinsic JSON(x::FldRatElt : nl:="\n") -> MonStgElt
  {
  Serialise a rational. If it's an integer, serialise as an integer, otherwise as a string.
  }
  return x in ZZ select IntegerToString(ZZ!x) else Sprintf("\"%o\"", x);
end intrinsic;

intrinsic JSON(x::RngIntResElt : nl:="\n") -> MonStgElt
  {
  Serialise an integer-mod, as an integer.
  }
  return IntegerToString(ZZ!x);
end intrinsic;

intrinsic JSON(x::FldFinElt : nl:="\n") -> MonStgElt
  {
  Serialise an element of a finite field of prime order, as an integer.
  }
  return IntegerToString(ZZ!x);
end intrinsic;

intrinsic JSON(x::RngUPolElt : nl:="\n") -> MonStgElt
  {
  Serialise an element of a univariate polynomial ring, as a sequence of integers.
  }
  B := BaseRing(Parent(x));
  if x in B then
    return JSON(B!x);
  else
    return JSON(Eltseq(x));
  end if;
end intrinsic;

intrinsic JSON(x::RngMPolElt : nl:="\n") -> MonStgElt
  {
  Serialise an element of a multivariate polynomial ring.
  }
  B := BaseRing(Parent(x));
  if x in B then
    return JSON(B!x);
  else
    c, m := CoefficientsAndMonomials(x);
    return JSON([* <"class", "RngMPolElt">, <"coeffs", c>, <"monomials", [ Exponents(p) : p in m]> *]);
  end if;
end intrinsic;

intrinsic JSON(x::FldFunRatElt : nl:="\n") -> MonStgElt
  {
  Serialise an element of a function field.
  }
  B := BaseRing(Parent(x));
  if x in B then
    return JSON(B!x);
  else
    return JSON([* <"class", "FldFunRatElt">, <"num", Numerator(x)>, <"denom", Denominator(x)> *]);
  end if;
end intrinsic;

intrinsic JSON(x::BoolElt : nl:="\n") -> MonStgElt
  {
  Serialise a Boolean.
  }
  return Sprintf("%o", x);
end intrinsic;

intrinsic JSON(x::Tup : nl:="\n") -> MonStgElt
  {
  Serialise an empty tuple, representing JSON null.
  }
  require #x eq 0 : "Only empty tuples (representing null) accepted in JSON";
  return "null";
end intrinsic;

// Permutations

intrinsic JSON(x::GrpPermElt : nl:="\n") -> MonStgElt
  {
  Serialise a permutation as a sequence.
  }
  return JSON(Eltseq(x) : nl:=nl);
end intrinsic;

// Matrices

intrinsic JSON(x::AlgMatElt : nl:="\n") -> MonStgElt
  {
  Serialise a matrix over QQ, GF(p), or ZZ as an array of arrays, or over a function field, or a polynomial ring in one variable, a class with ring, number of rows, number of columns and a sequence of values.
  }
  if NumberOfRows(x) eq 0 and NumberOfColumns(x) eq 0 then
    return "[ ]";
  end if;
  B := BaseRing(x);
  rs := [Eltseq(r):r in Rows(x)];
  if (IsField(B) and IsPrimeField(B)) or B cmpeq ZZ then
    strs := [[x in ZZ select IntegerToString(ZZ!x) else Sprintf("\"%o\"",x):x in r]:r in rs];
    f := Sprintf("%%%oo", Max([#s:s in r,r in strs]));
    strs := [[Sprintf(f,s):s in r]:r in strs];
    newnl := nl cat indent;
    return "[" cat newnl cat Join(["[ " cat Join(r, ", ") cat " ]":r in strs], "," cat newnl) cat nl cat "]";
  else
    vals := Eltseq(x);
    mat := [* <"class", "Matrix">,
            <"ring", Sprintf("%m", BaseRing(x))>,
            <"rows", NumberOfRows(x)>,
            <"columns", NumberOfColumns(x)>,
            <"values", vals >*];
    return JSON(mat: nl:=nl);
  end if;
end intrinsic;

intrinsic JSON(M::MtrxSprs : nl:="\n") -> MonStgElt
  {
  Serialise a sparse matrix (over QQ, GF(p), a function field, ZZ, or a polynomial ring in one variable) as a class with ring, number of rows, number of columns and a list of [r,c,v].
  }
  mat := [* <"class", "Sparse Matrix">,
            <"ring", Sprintf("%m", BaseRing(M))>,
            <"rows", NumberOfRows(M)>,
            <"columns", NumberOfColumns(M)>,
            <"values", [* [* t[1], t[2], t[3] *] : t in Eltseq(M)*]>*];

  return JSON(mat: nl:=nl);
end intrinsic;

// Useful functions for undoing JSONisation

intrinsic Keys(x::List) -> SeqEnum
  {
  Returns the sequence of indices of x.
  }
  return [1..#x];
end intrinsic;

intrinsic Numbers(x::Any) -> Any
  {
  Try to turn x into a rational or nested sequence of rationals.
  }
  if Type(x) eq List then
    // it is a nested sequence
    return [Numbers(y):y in x];
  elif Type(x) eq Assoc and x["class"] eq "Sparse Matrix" and x["rows"] eq 1 then
    // it is a vector in sparse form
    return Eltseq(SparseMatrix(eval(x["ring"]), x)[1]);
  elif Type(x) eq MonStgElt and Regexp("^0|-?[1-9][0-9]*(/[1-9][0-9]*)?$", x) then
    x := StringToRational(x);
    return x in ZZ select ZZ!x else x;
  elif Type(x) eq Assoc and "class" in Keys(x) and x["class"] eq "RngMPolElt" then
    c := Numbers(x["coeffs"]);
    m := Numbers(x["monomials"]);
    if #c eq 0 then
      return ZZ!0;
    end if;
    F := Universe(c);
    P := PolynomialRing(F, #m[1]);
    return Polynomial(c, [Monomial(P, p) : p in m]);
  elif Type(x) eq Assoc and "class" in Keys(x) and x["class"] eq "FldFunRatElt" then
    n := Numbers(x["num"]);
    d := Numbers(x["denom"]);
    // We need to find the correct base field to coerce them both into.
    // n is either a sequence, in which case it represents a polynomial, or a number, or is in a polynomial ring.
    Pd := Type(d) eq SeqEnum select Universe(d) else Parent(d);
    Pn := Type(n) eq SeqEnum select n eq [] select Pd else Universe(n) else Parent(n);
    
    if Type(n) eq SeqEnum or Type(d) eq SeqEnum then
      // We have a univariate polynomial ring
      B := Pn subset Pd select Pd else Pn;
      F := FunctionField(B);
    elif Type(n) eq RngMPolElt or Type(d) eq RngMPolElt then
      // One could be an integer type
      P := Type(d) eq RngMPolElt select Pd else Pn;
      F := FieldOfFractions(P);
    else
      // Both are numbers
      F := Pn subset Pd select Pd else Pn;
    end if;
    return F!n/F!d;
  else
    return x;
  end if;
end intrinsic;

intrinsic Num(x::Any) -> FldRatElt
  {
  Convert a string into a rational, or return x if it is not a string.
  }
  if Type(x) eq MonStgElt then
    return StringToRational(x);
  else
    return x;
  end if;
end intrinsic;

intrinsic Matrix(R::Rng, M::List) -> Mtrx
  {
  Convert a JSONised matrix into a matrix over R.
  }
  return Matrix(R, [[R!Numbers(x):x in r]:r in M]);
end intrinsic;

intrinsic Matrix(R::Rng, M::Assoc) -> Mtrx
  {
  Convert a JSONised matrix into a matrix over R.
  }
  keys := Keys(M);
  require "class" in keys and M["class"] in {"Matrix", "Sparse Matrix"}: "The file given does not encode a matrix.";
  if M["class"] eq "Sparse Matrix" then
    return Matrix(SparseMatrix(R, M));
  end if;
  
  require keys eq {"class", "ring", "rows", "columns", "values"}: "Invalid JSON format for a matrix";
  
  F := eval(M["ring"]);
  assert R eq F;
  n := Numbers(M["rows"]);
  m := Numbers(M["columns"]);
  
  return Matrix(F, n, m, [ F!Numbers(v) : v in M["values"]]);
end intrinsic;

intrinsic SparseMatrix(R::Rng, M::Assoc) -> MtrxSprs
  {
  Convert a JSONised sparse matrix into a sparse matrix over R.
  }
  keys := Keys(M);
  require "class" in keys and M["class"] eq "Sparse Matrix": "The file given does not encode a sparse matrix.";
  require keys eq {"class", "ring", "rows", "columns", "values"}: "Invalid JSON format for a sparse matrix";
  
  F := eval(M["ring"]);
  assert R eq F;
  n := Numbers(M["rows"]);
  m := Numbers(M["columns"]);
  
  return SparseMatrix(F, n, m, [ <x[1], x[2], Numbers(x[3])> : x in M["values"]]);
end intrinsic;
/*
Deserialisation

Uses external call to python to convert JSON to Magma—readable form.

Modifying this script?
Escape all double quote and backslash characters.
Don't use single quotes anywhere in the script!
*/
pyscript := "
import json
import re
from sys import stdin, version_info

if version_info[0] >= 3:
  long = int
  unicode = str

def escape(s):
  return \"\\\"\" + re.sub(r\"([\\\\\\\"])\", r\"\\\\\\1\", s) + \"\\\"\"

def magma(o):
  t = type(o)
  if t is int or t is long:
    return str(o)
  if t is str or t is unicode:
    return escape(o)
  if t is float:
    return str(o)
  if t is bool:
    return \"true\" if o else \"false\"
  if o is None:
    return \"null\"
  if t is list:
    return \"[*\" + \",\".join(magma(x) for x in o) + \"*]\"
  if t is dict:
    return \"dict([*\" + \",\".join(escape(k) + \",\" + magma(v) for k,v in o.items()) + \"*])\"
  raise TypeError(\"cannot Magmatise %s object\"%t)

o = json.load(stdin)

print(magma(o))
";

intrinsic ParseJSON(s::MonStgElt) -> Any
  {
  Deserialise a JSON string to an object.
  This uses a Python script to convert JSON to Magma-readable form.
  }
  function dict(l)
    d := AssociativeArray();
    for i in [1..#l by 2] do
      k := l[i]; v := l[i+1];
      assert k notin Keys(d);
      d[k] := v;
    end for;
    return d;
  end function;
  null := <>;
  inf := Infinity();
  nan := <"nan">;
  return eval(Pipe("python -c '" cat pyscript cat "'",s));
end intrinsic;
