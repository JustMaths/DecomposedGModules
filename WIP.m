intrinsic ChooseNiceBasis(A::ParAxlAlg) -> Mtrx
  {
  Returns the basis given by the indecomposibles of C direct sum the indecomposibles of V, where W = V \oplus C.
  }
  Vmod := sub<A`Wmod | Basis(A`V)>;
  ip := GetInnerProduct(A`Wmod);
  Cmod := Complement(A`Wmod, Vmod: ip:=ip);
  
  return Matrix(BaseRing(A), [ Eltseq(A`Wmod!u) : u in Basis(U), U in IndecomposableSummands(M), M in [Cmod, Vmod]]);
end intrinsic;

intrinsic ChangeBasis(A::ParAxlAlg, B::Mtrx) -> ParAxlAlg
  {
  Change of basis for A to the basis given by the rows of B.
  }
  Binv := B^-1;
  Wbas := VectorSpaceWithBasis(B);
  
  Anew := New(ParAxlAlg);
  
  Anew`group := A`group;
  Anew`Miyamoto_group := A`Miyamoto_group;
  Anew`GSet := A`GSet;
  Anew`tau := A`tau;
  Anew`shape := A`shape;
  Anew`number_of_axes := A`number_of_axes;
  Anew`fusion_table := A`fusion_table;
  
  Anew`Wmod := A`Wmod^(Binv);
  Anew`W := A`W;
  
  Anew`GSet_to_axes := map<Anew`GSet -> Anew`W | i:-> Coordinates(Wbas, i@A`GSet_to_axes)>;
  
  Vbas := [Coordinates(Wbas, v) : v in Basis(A`V)];
  Anew`V := sub<A`W | Vbas >;
  Anew`rels := {@ Anew`W | Coordinates(Wbas, u) : u in A`rels @};
  
  Vnewbas := Rows(Matrix(Basis(Anew`V))*B);
  mult := BulkMultiply(A, Vnewbas, Vnewbas);
  Anew`mult := [ Rows(Matrix(m)*Binv) : m in mult];
  
  Bmap := hom<A`W -> Anew`W | Binv>;
  UpdateAxes(A, ~Anew, Bmap : matrix := Binv);
  
  UpdateSubalgebras(A, ~Anew, Bmap);
  
  return Anew;
end intrinsic;
