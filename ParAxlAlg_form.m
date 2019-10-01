/*

=========== Code to find Frobenius form =============

*/
import "ParAxlAlg_initial.m": EigenvalueSort;

function ShiftProducts(L,M)
  if Type(L) eq RngIntElt then
    return [*L*],M;
  end if;
  while #L eq 2 do
    M := [* L[2], M *];
    if Type(L[1]) ne RngIntElt then
      L := L[1];
    else
      L := [*L[1]*];
    end if;
  end while;
  return L, M;
end function;
    
function NestedDepth(L)
  if Type(L) eq RngIntElt then
    return 0;
  else
    return Max(NestedDepth(L[1]), NestedDepth(L[2]))+1;
  end if;
end function;
    
function RecursiveSort(L)
  if Type(L) eq RngIntElt then
    return L;
  end if;
  if Type(L[1]) eq Type(L[2]) and Type(L[1]) eq RngIntElt then
    if L[1] le L[2] then return L;
    else return [*L[2], L[1]*];
    end if;
  end if;
  if NestedDepth(L[2]) lt NestedDepth(L[1]) then
    L := [* L[2], L[1] *];
  end if;
  return [* RecursiveSort(L[1]), RecursiveSort(L[2])*];
end function;

function mLength(L)
  if Type(L) eq RngIntElt then
    return 1;
  else
    return mLength(L[1])+ mLength(L[2]);
  end if;
end function;

function FindProduct(A, prods, L)
  // assume that prods is a list of the products up to length m
  if Type(L) eq RngIntElt then
    return prods[1,L,2];
  end if;
  m := #prods;
  d := mLength(L);
  L := RecursiveSort(L);
  if d lt m then
    // we have already calculated this product
    assert exists(v){ prods[d,k,2] : k in [1..#prods[d]] | L eq prods[d,k,1]};
    return v;
  else
    x := FindProduct(A, prods, L[1]);
    y := FindProduct(A, prods, L[2]);
    return (A!x*A!y)`elt;
  end if;
end function;

function Dedupe(L)
  out := [];
  // build hashes
  hashes := { Hash(l) : l in L};
  outhash := {};
  for l in L do
    lhash := Hash(l);
    if lhash notin outhash then
      Include(~outhash, lhash);
      Append(~out,l);
    else
      if l notin out then
        Append(~out,l);
      end if;
    end if;
  end for;
  return out;
end function;
/*

Find the Frobenius form and also m-closed

*/
intrinsic HasFrobeniusForm(A::ParAxlAlg) -> BoolElt, AlgMatElt, RngIntElt
  {
  Checks to see if an alternative bilinear form exists and if so returns it and the m for which A is m-closed.
  }
  require A`V eq A`W: "Can't calculate m-closed before calculating the algebra!.";
  if Dimension(A) eq 0 then
    return false,_,0;
  end if;
  G := Group(A);
  W := A`W;
  
  Ax := A`GSet;
  // We form the orbits, sorting them in the order in the order from Ax.
  orbs := Sort([ Sort(o) : o in Orbits(G, Ax)], func<x,y|x[1]-y[1]>);
  axes := Setseq(&join [ o@A`GSet_to_axes : o in orbs]);
  conjs := [ [ g where _, g := IsConjugate(G, Ax, o[1], o[j]) : j in [1..#o]] : o in orbs];
  
  U := sub<W | axes>;
  // We build a basis
  // These are a sequence of tuples <m, j, v>, where v is the element which is the jth element in the mth level of prods.
  bas := [ < 1, i, axes[i] >: i in [1..#axes]];
  // We also maintain a list of products we have seen before
  // These are a list sequences of tuples.  The sequences are the number of axes multiplied together.  Each tuple is of the form <S, v>, where v is the answer and S is a list of lists of indexes of axes, representing the multiplication of those axes with brackets given by the lists (no list means no multiplication ie a single axis).
  prods := [*[< i, axes[i] > : i in [1..#axes]]*];
  
  m := 1;
  while Dimension(U) ne Dimension(W) do
    m +:=1;
    // Multiplication is commutative, so we just need to do all pairs up to half the dimension
    newshell := [ BulkMultiply(A, [p[2] : p in prods[i]],
             [p[2] : p in prods[m-i]]) : i in [1..Floor(m/2)]];
    // Build the sequence of axes which multiply to give the new products
    newprods := [ < RecursiveSort([*prods[i,j,1], prods[m-i,k,1]*]), newshell[i,j,k]> : k in [1..#newshell[i,j]], j in [1..#newshell[i]], i in [1..Floor(m/2)] ];
    
    // attempt to dedupe quickly
    if m eq 2 then
      newprods := Dedupe(newprods);
    end if;
    
    UU := sub<W| Flat(newshell)>;
    Append(~prods, newprods);
    U +:= UU;
    // We build a basis as we go along
    // We speed things up by working in the quotient
    Q, quo := quo<U|[t[3] : t in bas]>;
    Qprods := [ <j, newprods[j,2]> : j in [1..#newprods] ];
    while Dimension(Q) ne 0 do
      Qprods := [ <Qprods[j,1], v> : j in [1..#Qprods] | not IsZero(v) where v := Qprods[j,2]@quo ];
      j, newvector := Explode(Qprods[1]);
      Append(~bas, <m,j,newprods[j,2]>);
      Q, quo := quo<Q| newvector>;    
    end while;
  end while;
  
  // We now extend our products to make calculating the Frobenius form quicker
  vprint ParAxlAlg, 4: "Extending the products.";
  // We find how long a products we need to calculate
  num := #{ b : b in bas | b[1] eq m};
  assert num ge 1;
  if num eq 1 then
    limit := 2*m-2;
  else
    limit := 2*m-1;
  end if;
  
  // Seems that calculating many products uses too much memory and might be slow anyway.
  // For the mmoment, just set mm =3
  // Could collect all necessary products together and then do them in a matrix calc?
  
  limit := 3;
  mm := m;
  while #prods lt limit do
    mm +:=1;
    newshell := [ BulkMultiply(A, [p[2] : p in prods[i]],
             [p[2] : p in prods[mm-i]]) : i in [1..Floor(mm/2)]];
    // Build the sequence of axes which multiply to give the new products
    newprods := [ < RecursiveSort([*prods[i,j,1], prods[mm-i,k,1]*]), newshell[i,j,k]> : k in [1..#newshell[i,j]], j in [1..#newshell[i]], i in [1..Floor(mm/2)] ];
    
    Append(~prods, newprods);
  end while;
  
  vprint ParAxlAlg, 4: "Building the form.";
  
  // We now build the Frobenius form with respect to our basis.

  // precompute the bases for each axis
  max_size := Max([#S : S in Keys(A`axes[1]`even)]);
  assert exists(evens){S : S in Keys(A`axes[1]`even) | #S eq max_size};
  max_size := Max([#S : S in Keys(A`axes[1]`odd)]);
  assert exists(odds){S : S in Keys(A`axes[1]`odd) | #S eq max_size};
  
  evens := [ {@ s @} : s in Sort(evens, EigenvalueSort)];
  odds := [ {@ s @} : s in Sort(odds, EigenvalueSort)];
  actionhom := GModuleAction(A`Wmod);
  Axbas := [ &cat[ k[1] eq 1 select ExtendBasis([A`axes[i]`id`elt], A`axes[i]`even[k]) else Basis(A`axes[i]`even[k]) : k in evens]
         cat &cat[ Basis(A`axes[i]`odd[k]): k in odds] : i in [1..#A`axes] ];
  Axbas := [ RSpaceWithBasis(FastMatrix(Axbas[i], g@actionhom)) : g in conjs[i], i in [1..#Axbas]];

  form := [[] : i in [1..#bas]];
  for i in [1..#bas] do
    im, ii, _ := Explode(bas[i]);
    for j in [1..i] do
      jm, jj, _ := Explode(bas[j]);
      a, L := ShiftProducts(prods[jm,jj,1], prods[im,ii,1]);
      v := FindProduct(A, prods, L);
      form[i,j] := Coordinates(Axbas[a[1]],v)[1];
    end for;
  end for;
  form := SymmetricMatrix(&cat form);
  
  vprint ParAxlAlg, 4: "Checking the form.";
  // To check form just need to check on a basis
  // Since (i,jk) = (ij,k) implies (k,ji) = (kj,i) just need to check for k \leq i
  stdbas := Basis(W);
  std_to_bas := Matrix([t[3] : t in bas]);
  bas_to_std := std_to_bas^-1;
  
  // precompute the matrices of all the bas[j]*bas[k]
  
  Mjs := [[] : j in [1..#bas]];
  for j in [1..#bas] do
    jm, jj, _ := Explode(bas[j]);
    for k in [1..#bas] do
      km, kk, _ := Explode(bas[k]);
      Mjs[j][k] := FindProduct(A, prods, RecursiveSort([*prods[jm,jj,1],prods[km,kk,1]*]));
    end for;
  end for;
  Mjs := [Matrix(M) : M in Mjs];
  
  // Now, to check (e_i,e_j*e_k) = (e_i*e_j, e_k), build matrices over i and k

  for j in [1..#bas] do
    if form*Transpose(Mjs[j]*bas_to_std) ne Mjs[j]*bas_to_std*form then
      return false, _, m;
    end if;
  end for;
    
  return true, bas_to_std*form*Transpose(bas_to_std), m;
end intrinsic;
