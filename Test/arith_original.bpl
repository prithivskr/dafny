
const $$Language$Dafny: bool
uses {
axiom $$Language$Dafny;
}

type Ty;

type Bv0 = int;

const unique TBool: Ty
uses {
axiom Tag(TBool) == TagBool;
}

const unique TChar: Ty
uses {
axiom Tag(TChar) == TagChar;
}

const unique TInt: Ty
uses {
axiom Tag(TInt) == TagInt;
}

const unique TField: Ty
uses {
axiom Tag(TField) == TagField;
}

const unique TReal: Ty
uses {
axiom Tag(TReal) == TagReal;
}

const unique TORDINAL: Ty
uses {
axiom Tag(TORDINAL) == TagORDINAL;
}

revealed function TBitvector(int) : Ty;

axiom (forall w: int :: { TBitvector(w) } Inv0_TBitvector(TBitvector(w)) == w);

revealed function TSet(Ty) : Ty;

axiom (forall t: Ty :: { TSet(t) } Inv0_TSet(TSet(t)) == t);

axiom (forall t: Ty :: { TSet(t) } Tag(TSet(t)) == TagSet);

revealed function TISet(Ty) : Ty;

axiom (forall t: Ty :: { TISet(t) } Inv0_TISet(TISet(t)) == t);

axiom (forall t: Ty :: { TISet(t) } Tag(TISet(t)) == TagISet);

revealed function TMultiSet(Ty) : Ty;

axiom (forall t: Ty :: { TMultiSet(t) } Inv0_TMultiSet(TMultiSet(t)) == t);

axiom (forall t: Ty :: { TMultiSet(t) } Tag(TMultiSet(t)) == TagMultiSet);

revealed function TSeq(Ty) : Ty;

axiom (forall t: Ty :: { TSeq(t) } Inv0_TSeq(TSeq(t)) == t);

axiom (forall t: Ty :: { TSeq(t) } Tag(TSeq(t)) == TagSeq);

revealed function TMap(Ty, Ty) : Ty;

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Inv0_TMap(TMap(t, u)) == t);

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Inv1_TMap(TMap(t, u)) == u);

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Tag(TMap(t, u)) == TagMap);

revealed function TIMap(Ty, Ty) : Ty;

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Inv0_TIMap(TIMap(t, u)) == t);

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Inv1_TIMap(TIMap(t, u)) == u);

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Tag(TIMap(t, u)) == TagIMap);

revealed function Inv0_TBitvector(Ty) : int;

revealed function Inv0_TSet(Ty) : Ty;

revealed function Inv0_TISet(Ty) : Ty;

revealed function Inv0_TSeq(Ty) : Ty;

revealed function Inv0_TMultiSet(Ty) : Ty;

revealed function Inv0_TMap(Ty) : Ty;

revealed function Inv1_TMap(Ty) : Ty;

revealed function Inv0_TIMap(Ty) : Ty;

revealed function Inv1_TIMap(Ty) : Ty;

type TyTag;

revealed function Tag(Ty) : TyTag;

const unique TagBool: TyTag;

const unique TagChar: TyTag;

const unique TagInt: TyTag;

const unique TagField: TyTag;

const unique TagReal: TyTag;

const unique TagORDINAL: TyTag;

const unique TagSet: TyTag;

const unique TagISet: TyTag;

const unique TagMultiSet: TyTag;

const unique TagSeq: TyTag;

const unique TagMap: TyTag;

const unique TagIMap: TyTag;

const unique TagClass: TyTag;

type TyTagFamily;

revealed function TagFamily(Ty) : TyTagFamily;

revealed function {:identity} Lit<T>(x: T) : T
uses {
axiom (forall<T> x: T :: {:identity} { Lit(x): T } Lit(x): T == x);
}

axiom (forall<T> x: T :: { $Box(Lit(x)) } $Box(Lit(x)) == Lit($Box(x)));

revealed function {:identity} LitInt(x: int) : int
uses {
axiom (forall x: int :: {:identity} { LitInt(x): int } LitInt(x): int == x);
}

axiom (forall x: int :: { $Box(LitInt(x)) } $Box(LitInt(x)) == Lit($Box(x)));

revealed function {:identity} LitReal(x: real) : real
uses {
axiom (forall x: real :: {:identity} { LitReal(x): real } LitReal(x): real == x);
}

axiom (forall x: real :: { $Box(LitReal(x)) } $Box(LitReal(x)) == Lit($Box(x)));

revealed function {:inline} char#IsChar(n: int) : bool
{
  (0 <= n && n < 55296) || (57344 <= n && n < 1114112)
}

type char;

revealed function char#FromInt(int) : char;

axiom (forall n: int :: 
  { char#FromInt(n) } 
  char#IsChar(n) ==> char#ToInt(char#FromInt(n)) == n);

revealed function char#ToInt(char) : int;

axiom (forall ch: char :: 
  { char#ToInt(ch) } 
  char#FromInt(char#ToInt(ch)) == ch && char#IsChar(char#ToInt(ch)));

revealed function char#Plus(char, char) : char;

axiom (forall a: char, b: char :: 
  { char#Plus(a, b) } 
  char#Plus(a, b) == char#FromInt(char#ToInt(a) + char#ToInt(b)));

revealed function char#Minus(char, char) : char;

axiom (forall a: char, b: char :: 
  { char#Minus(a, b) } 
  char#Minus(a, b) == char#FromInt(char#ToInt(a) - char#ToInt(b)));

type ref;

const null: ref;

const locals: ref;

type FieldFamily;

const unique object_field: FieldFamily;

revealed function field_depth(f: Field) : int;

revealed function field_family(f: Field) : FieldFamily;

revealed function local_field(ff: FieldFamily, depth: int) : Field
uses {
axiom (forall ff: FieldFamily, depth: int :: 
  {:trigger local_field(ff, depth)} 
  field_depth(local_field(ff, depth)) == depth
     && field_family(local_field(ff, depth)) == ff);
}

type Box;

const $ArbitraryBoxValue: Box;

revealed function $Box<T>(T) : Box;

revealed function $Unbox<T>(Box) : T;

axiom (forall<T> x: T :: {:weight 3} { $Box(x) } $Unbox($Box(x)) == x);

axiom (forall<T> x: Box :: { $Unbox(x): T } $Box($Unbox(x): T) == x);

revealed function $IsBox(Box, Ty) : bool;

revealed function $IsAllocBox(Box, Ty, Heap) : bool;

axiom (forall bx: Box :: 
  { $IsBox(bx, TInt) } 
  $IsBox(bx, TInt) ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, TInt));

axiom (forall bx: Box :: 
  { $IsBox(bx, TReal) } 
  $IsBox(bx, TReal)
     ==> $Box($Unbox(bx): real) == bx && $Is($Unbox(bx): real, TReal));

axiom (forall bx: Box :: 
  { $IsBox(bx, TBool) } 
  $IsBox(bx, TBool)
     ==> $Box($Unbox(bx): bool) == bx && $Is($Unbox(bx): bool, TBool));

axiom (forall bx: Box :: 
  { $IsBox(bx, TChar) } 
  $IsBox(bx, TChar)
     ==> $Box($Unbox(bx): char) == bx && $Is($Unbox(bx): char, TChar));

axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(0)) } 
  $IsBox(bx, TBitvector(0))
     ==> $Box($Unbox(bx): Bv0) == bx && $Is($Unbox(bx): Bv0, TBitvector(0)));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TSet(t)) } 
  $IsBox(bx, TSet(t))
     ==> $Box($Unbox(bx): Set) == bx && $Is($Unbox(bx): Set, TSet(t)));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TISet(t)) } 
  $IsBox(bx, TISet(t))
     ==> $Box($Unbox(bx): ISet) == bx && $Is($Unbox(bx): ISet, TISet(t)));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TMultiSet(t)) } 
  $IsBox(bx, TMultiSet(t))
     ==> $Box($Unbox(bx): MultiSet) == bx && $Is($Unbox(bx): MultiSet, TMultiSet(t)));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TSeq(t)) } 
  $IsBox(bx, TSeq(t))
     ==> $Box($Unbox(bx): Seq) == bx && $Is($Unbox(bx): Seq, TSeq(t)));

axiom (forall bx: Box, s: Ty, t: Ty :: 
  { $IsBox(bx, TMap(s, t)) } 
  $IsBox(bx, TMap(s, t))
     ==> $Box($Unbox(bx): Map) == bx && $Is($Unbox(bx): Map, TMap(s, t)));

axiom (forall bx: Box, s: Ty, t: Ty :: 
  { $IsBox(bx, TIMap(s, t)) } 
  $IsBox(bx, TIMap(s, t))
     ==> $Box($Unbox(bx): IMap) == bx && $Is($Unbox(bx): IMap, TIMap(s, t)));

axiom (forall<T> v: T, t: Ty :: 
  { $IsBox($Box(v), t) } 
  $IsBox($Box(v), t) <==> $Is(v, t));

axiom (forall<T> v: T, t: Ty, h: Heap :: 
  { $IsAllocBox($Box(v), t, h) } 
  $IsAllocBox($Box(v), t, h) <==> $IsAlloc(v, t, h));

revealed function $Is<T>(T, Ty) : bool;

axiom (forall v: int :: { $Is(v, TInt) } $Is(v, TInt));

axiom (forall v: real :: { $Is(v, TReal) } $Is(v, TReal));

axiom (forall v: bool :: { $Is(v, TBool) } $Is(v, TBool));

axiom (forall v: char :: { $Is(v, TChar) } $Is(v, TChar));

axiom (forall v: Field :: { $Is(v, TField) } $Is(v, TField));

axiom (forall v: ORDINAL :: { $Is(v, TORDINAL) } $Is(v, TORDINAL));

axiom (forall v: Bv0 :: { $Is(v, TBitvector(0)) } $Is(v, TBitvector(0)));

axiom (forall v: Set, t0: Ty :: 
  { $Is(v, TSet(t0)) } 
  $Is(v, TSet(t0))
     <==> (forall bx: Box :: 
      { Set#IsMember(v, bx) } 
      Set#IsMember(v, bx) ==> $IsBox(bx, t0)));

axiom (forall v: ISet, t0: Ty :: 
  { $Is(v, TISet(t0)) } 
  $Is(v, TISet(t0)) <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsBox(bx, t0)));

axiom (forall v: MultiSet, t0: Ty :: 
  { $Is(v, TMultiSet(t0)) } 
  $Is(v, TMultiSet(t0))
     <==> (forall bx: Box :: 
      { MultiSet#Multiplicity(v, bx) } 
      0 < MultiSet#Multiplicity(v, bx) ==> $IsBox(bx, t0)));

axiom (forall v: MultiSet, t0: Ty :: 
  { $Is(v, TMultiSet(t0)) } 
  $Is(v, TMultiSet(t0)) ==> $IsGoodMultiSet(v));

axiom (forall v: Seq, t0: Ty :: 
  { $Is(v, TSeq(t0)) } 
  $Is(v, TSeq(t0))
     <==> (forall i: int :: 
      { Seq#Index(v, i) } 
      0 <= i && i < Seq#Length(v) ==> $IsBox(Seq#Index(v, i), t0)));

axiom (forall v: Map, t0: Ty, t1: Ty :: 
  { $Is(v, TMap(t0, t1)) } 
  $Is(v, TMap(t0, t1))
     <==> (forall bx: Box :: 
      { Map#Elements(v)[bx] } { Set#IsMember(Map#Domain(v), bx) } 
      Set#IsMember(Map#Domain(v), bx)
         ==> $IsBox(Map#Elements(v)[bx], t1) && $IsBox(bx, t0)));

axiom (forall v: Map, t0: Ty, t1: Ty :: 
  { $Is(v, TMap(t0, t1)) } 
  $Is(v, TMap(t0, t1))
     ==> $Is(Map#Domain(v), TSet(t0))
       && $Is(Map#Values(v), TSet(t1))
       && $Is(Map#Items(v), TSet(Tclass._System.Tuple2(t0, t1))));

axiom (forall v: IMap, t0: Ty, t1: Ty :: 
  { $Is(v, TIMap(t0, t1)) } 
  $Is(v, TIMap(t0, t1))
     <==> (forall bx: Box :: 
      { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] } 
      IMap#Domain(v)[bx] ==> $IsBox(IMap#Elements(v)[bx], t1) && $IsBox(bx, t0)));

axiom (forall v: IMap, t0: Ty, t1: Ty :: 
  { $Is(v, TIMap(t0, t1)) } 
  $Is(v, TIMap(t0, t1))
     ==> $Is(IMap#Domain(v), TISet(t0))
       && $Is(IMap#Values(v), TISet(t1))
       && $Is(IMap#Items(v), TISet(Tclass._System.Tuple2(t0, t1))));

revealed function $IsAlloc<T>(T, Ty, Heap) : bool;

axiom (forall h: Heap, v: int :: { $IsAlloc(v, TInt, h) } $IsAlloc(v, TInt, h));

axiom (forall h: Heap, v: real :: { $IsAlloc(v, TReal, h) } $IsAlloc(v, TReal, h));

axiom (forall h: Heap, v: bool :: { $IsAlloc(v, TBool, h) } $IsAlloc(v, TBool, h));

axiom (forall h: Heap, v: char :: { $IsAlloc(v, TChar, h) } $IsAlloc(v, TChar, h));

axiom (forall h: Heap, v: ORDINAL :: 
  { $IsAlloc(v, TORDINAL, h) } 
  $IsAlloc(v, TORDINAL, h));

axiom (forall v: Bv0, h: Heap :: 
  { $IsAlloc(v, TBitvector(0), h) } 
  $IsAlloc(v, TBitvector(0), h));

axiom (forall v: Set, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TSet(t0), h) } 
  $IsAlloc(v, TSet(t0), h)
     <==> (forall bx: Box :: 
      { Set#IsMember(v, bx) } 
      Set#IsMember(v, bx) ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: ISet, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TISet(t0), h) } 
  $IsAlloc(v, TISet(t0), h)
     <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: MultiSet, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TMultiSet(t0), h) } 
  $IsAlloc(v, TMultiSet(t0), h)
     <==> (forall bx: Box :: 
      { MultiSet#Multiplicity(v, bx) } 
      0 < MultiSet#Multiplicity(v, bx) ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: Seq, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TSeq(t0), h) } 
  $IsAlloc(v, TSeq(t0), h)
     <==> (forall i: int :: 
      { Seq#Index(v, i) } 
      0 <= i && i < Seq#Length(v) ==> $IsAllocBox(Seq#Index(v, i), t0, h)));

axiom (forall v: Map, t0: Ty, t1: Ty, h: Heap :: 
  { $IsAlloc(v, TMap(t0, t1), h) } 
  $IsAlloc(v, TMap(t0, t1), h)
     <==> (forall bx: Box :: 
      { Map#Elements(v)[bx] } { Set#IsMember(Map#Domain(v), bx) } 
      Set#IsMember(Map#Domain(v), bx)
         ==> $IsAllocBox(Map#Elements(v)[bx], t1, h) && $IsAllocBox(bx, t0, h)));

axiom (forall v: IMap, t0: Ty, t1: Ty, h: Heap :: 
  { $IsAlloc(v, TIMap(t0, t1), h) } 
  $IsAlloc(v, TIMap(t0, t1), h)
     <==> (forall bx: Box :: 
      { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] } 
      IMap#Domain(v)[bx]
         ==> $IsAllocBox(IMap#Elements(v)[bx], t1, h) && $IsAllocBox(bx, t0, h)));

revealed function $AlwaysAllocated(Ty) : bool;

axiom (forall ty: Ty :: 
  { $AlwaysAllocated(ty) } 
  $AlwaysAllocated(ty)
     ==> (forall h: Heap, v: Box :: 
      { $IsAllocBox(v, ty, h) } 
      $IsBox(v, ty) ==> $IsAllocBox(v, ty, h)));

revealed function $OlderTag(Heap) : bool;

type ClassName;

const unique class._System.int: ClassName;

const unique class._System.bool: ClassName;

const unique class._System.set: ClassName;

const unique class._System.seq: ClassName;

const unique class._System.multiset: ClassName;

revealed function Tclass._System.object?() : Ty
uses {
// Tclass._System.object? Tag
axiom Tag(Tclass._System.object?()) == Tagclass._System.object?
   && TagFamily(Tclass._System.object?()) == tytagFamily$object;
}

revealed function Tclass._System.Tuple2(Ty, Ty) : Ty;

revealed function dtype(ref) : Ty;

revealed function TypeTuple(a: ClassName, b: ClassName) : ClassName;

revealed function TypeTupleCar(ClassName) : ClassName;

revealed function TypeTupleCdr(ClassName) : ClassName;

axiom (forall a: ClassName, b: ClassName :: 
  { TypeTuple(a, b) } 
  TypeTupleCar(TypeTuple(a, b)) == a && TypeTupleCdr(TypeTuple(a, b)) == b);

type HandleType;

revealed function SetRef_to_SetBox(s: [ref]bool) : Set;

axiom (forall s: [ref]bool, bx: Box :: 
  { Set#IsMember(SetRef_to_SetBox(s), bx) } 
  Set#IsMember(SetRef_to_SetBox(s), bx) == s[$Unbox(bx): ref]);

axiom (forall s: [ref]bool :: 
  { SetRef_to_SetBox(s) } 
  $Is(SetRef_to_SetBox(s), TSet(Tclass._System.object?())));

revealed function Apply1(Ty, Ty, Heap, HandleType, Box) : Box;

type DatatypeType;

type DtCtorId;

revealed function DatatypeCtorId(DatatypeType) : DtCtorId;

revealed function DtRank(DatatypeType) : int;

revealed function BoxRank(Box) : int;

axiom (forall d: DatatypeType :: { BoxRank($Box(d)) } BoxRank($Box(d)) == DtRank(d));

type ORDINAL = Box;

revealed function ORD#IsNat(ORDINAL) : bool;

revealed function ORD#Offset(ORDINAL) : int;

axiom (forall o: ORDINAL :: { ORD#Offset(o) } 0 <= ORD#Offset(o));

revealed function {:inline} ORD#IsLimit(o: ORDINAL) : bool
{
  ORD#Offset(o) == 0
}

revealed function {:inline} ORD#IsSucc(o: ORDINAL) : bool
{
  0 < ORD#Offset(o)
}

revealed function ORD#FromNat(int) : ORDINAL;

axiom (forall n: int :: 
  { ORD#FromNat(n) } 
  0 <= n ==> ORD#IsNat(ORD#FromNat(n)) && ORD#Offset(ORD#FromNat(n)) == n);

axiom (forall o: ORDINAL :: 
  { ORD#Offset(o) } { ORD#IsNat(o) } 
  ORD#IsNat(o) ==> o == ORD#FromNat(ORD#Offset(o)));

revealed function ORD#Less(ORDINAL, ORDINAL) : bool;

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Less(o, p) } 
  (ORD#Less(o, p) ==> o != p)
     && (ORD#IsNat(o) && !ORD#IsNat(p) ==> ORD#Less(o, p))
     && (ORD#IsNat(o) && ORD#IsNat(p)
       ==> ORD#Less(o, p) == (ORD#Offset(o) < ORD#Offset(p)))
     && (ORD#Less(o, p) && ORD#IsNat(p) ==> ORD#IsNat(o)));

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Less(o, p), ORD#Less(p, o) } 
  ORD#Less(o, p) || o == p || ORD#Less(p, o));

axiom (forall o: ORDINAL, p: ORDINAL, r: ORDINAL :: 
  { ORD#Less(o, p), ORD#Less(p, r) } { ORD#Less(o, p), ORD#Less(o, r) } 
  ORD#Less(o, p) && ORD#Less(p, r) ==> ORD#Less(o, r));

revealed function ORD#LessThanLimit(ORDINAL, ORDINAL) : bool;

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#LessThanLimit(o, p) } 
  ORD#LessThanLimit(o, p) == ORD#Less(o, p));

revealed function ORD#Plus(ORDINAL, ORDINAL) : ORDINAL;

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Plus(o, p) } 
  (ORD#IsNat(ORD#Plus(o, p)) ==> ORD#IsNat(o) && ORD#IsNat(p))
     && (ORD#IsNat(p)
       ==> ORD#IsNat(ORD#Plus(o, p)) == ORD#IsNat(o)
         && ORD#Offset(ORD#Plus(o, p)) == ORD#Offset(o) + ORD#Offset(p)));

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Plus(o, p) } 
  (o == ORD#Plus(o, p) || ORD#Less(o, ORD#Plus(o, p)))
     && (p == ORD#Plus(o, p) || ORD#Less(p, ORD#Plus(o, p))));

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Plus(o, p) } 
  (o == ORD#FromNat(0) ==> ORD#Plus(o, p) == p)
     && (p == ORD#FromNat(0) ==> ORD#Plus(o, p) == o));

revealed function ORD#Minus(ORDINAL, ORDINAL) : ORDINAL;

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Minus(o, p) } 
  ORD#IsNat(p) && ORD#Offset(p) <= ORD#Offset(o)
     ==> ORD#IsNat(ORD#Minus(o, p)) == ORD#IsNat(o)
       && ORD#Offset(ORD#Minus(o, p)) == ORD#Offset(o) - ORD#Offset(p));

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Minus(o, p) } 
  ORD#IsNat(p) && ORD#Offset(p) <= ORD#Offset(o)
     ==> (p == ORD#FromNat(0) && ORD#Minus(o, p) == o)
       || (p != ORD#FromNat(0) && ORD#Less(ORD#Minus(o, p), o)));

axiom (forall o: ORDINAL, m: int, n: int :: 
  { ORD#Plus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) } 
  0 <= m && 0 <= n
     ==> ORD#Plus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n))
       == ORD#Plus(o, ORD#FromNat(m + n)));

axiom (forall o: ORDINAL, m: int, n: int :: 
  { ORD#Minus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) } 
  0 <= m && 0 <= n && m + n <= ORD#Offset(o)
     ==> ORD#Minus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n))
       == ORD#Minus(o, ORD#FromNat(m + n)));

axiom (forall o: ORDINAL, m: int, n: int :: 
  { ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) } 
  0 <= m && 0 <= n && n <= ORD#Offset(o) + m
     ==> (0 <= m - n
         ==> ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Plus(o, ORD#FromNat(m - n)))
       && (m - n <= 0
         ==> ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Minus(o, ORD#FromNat(n - m))));

axiom (forall o: ORDINAL, m: int, n: int :: 
  { ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) } 
  0 <= m && 0 <= n && n <= ORD#Offset(o) + m
     ==> (0 <= m - n
         ==> ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Minus(o, ORD#FromNat(m - n)))
       && (m - n <= 0
         ==> ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Plus(o, ORD#FromNat(n - m))));

type LayerType;

const $LZ: LayerType;

revealed function $LS(LayerType) : LayerType;

revealed function AsFuelBottom(LayerType) : LayerType;

revealed function AtLayer<A>([LayerType]A, LayerType) : A;

axiom (forall<A> f: [LayerType]A, ly: LayerType :: 
  { AtLayer(f, ly) } 
  AtLayer(f, ly) == f[ly]);

axiom (forall<A> f: [LayerType]A, ly: LayerType :: 
  { AtLayer(f, $LS(ly)) } 
  AtLayer(f, $LS(ly)) == AtLayer(f, ly));

type Field;

revealed function FDim(Field) : int
uses {
axiom FDim(alloc) == 0;
}

revealed function IndexField(int) : Field;

axiom (forall i: int :: { IndexField(i) } FDim(IndexField(i)) == 1);

revealed function IndexField_Inverse(Field) : int;

axiom (forall i: int :: { IndexField(i) } IndexField_Inverse(IndexField(i)) == i);

revealed function MultiIndexField(Field, int) : Field;

axiom (forall f: Field, i: int :: 
  { MultiIndexField(f, i) } 
  FDim(MultiIndexField(f, i)) == FDim(f) + 1);

revealed function MultiIndexField_Inverse0(Field) : Field;

revealed function MultiIndexField_Inverse1(Field) : int;

axiom (forall f: Field, i: int :: 
  { MultiIndexField(f, i) } 
  MultiIndexField_Inverse0(MultiIndexField(f, i)) == f
     && MultiIndexField_Inverse1(MultiIndexField(f, i)) == i);

revealed function DeclType(Field) : ClassName;

type NameFamily;

revealed function DeclName(Field) : NameFamily
uses {
axiom DeclName(alloc) == allocName;
}

revealed function FieldOfDecl(ClassName, NameFamily) : Field;

axiom (forall cl: ClassName, nm: NameFamily :: 
  { FieldOfDecl(cl, nm): Field } 
  DeclType(FieldOfDecl(cl, nm): Field) == cl
     && DeclName(FieldOfDecl(cl, nm): Field) == nm);

revealed function $IsGhostField(Field) : bool
uses {
axiom $IsGhostField(alloc);
}

axiom (forall h: Heap, k: Heap :: 
  { $HeapSuccGhost(h, k) } 
  $HeapSuccGhost(h, k)
     ==> $HeapSucc(h, k)
       && (forall o: ref, f: Field :: 
        { read(k, o, f) } 
        !$IsGhostField(f) ==> read(h, o, f) == read(k, o, f)));

axiom (forall<T> h: Heap, k: Heap, v: T, t: Ty :: 
  { $HeapSucc(h, k), $IsAlloc(v, t, h) } 
  $HeapSucc(h, k) ==> $IsAlloc(v, t, h) ==> $IsAlloc(v, t, k));

axiom (forall h: Heap, k: Heap, bx: Box, t: Ty :: 
  { $HeapSucc(h, k), $IsAllocBox(bx, t, h) } 
  $HeapSucc(h, k) ==> $IsAllocBox(bx, t, h) ==> $IsAllocBox(bx, t, k));

const unique alloc: Field;

const unique allocName: NameFamily;

revealed function _System.array.Length(a: ref) : int;

axiom (forall o: ref :: { _System.array.Length(o) } 0 <= _System.array.Length(o));

revealed function Int(x: real) : int
uses {
axiom (forall x: real :: { Int(x): int } Int(x): int == int(x));
}

revealed function {:inline} Real(x: int) : real
{
  real(x)
}

axiom (forall i: int :: { Int(Real(i)) } Int(Real(i)) == i);

revealed function {:inline} _System.real.Floor(x: real) : int
{
  Int(x)
}

type Heap = [ref][Field]Box;

revealed function {:inline} read(H: Heap, r: ref, f: Field) : Box
{
  H[r][f]
}

revealed function {:inline} update(H: Heap, r: ref, f: Field, v: Box) : Heap
{
  H[r := H[r][f := v]]
}

revealed function $IsGoodHeap(Heap) : bool;

revealed function $IsHeapAnchor(Heap) : bool;

var $Heap: Heap where $IsGoodHeap($Heap) && $IsHeapAnchor($Heap);

const $OneHeap: Heap
uses {
axiom $IsGoodHeap($OneHeap);
}

revealed function $HeapSucc(Heap, Heap) : bool;

axiom (forall h: Heap, r: ref, f: Field, x: Box :: 
  { update(h, r, f, x) } 
  $IsGoodHeap(update(h, r, f, x)) ==> $HeapSucc(h, update(h, r, f, x)));

axiom (forall a: Heap, b: Heap, c: Heap :: 
  { $HeapSucc(a, b), $HeapSucc(b, c) } 
  a != c ==> $HeapSucc(a, b) && $HeapSucc(b, c) ==> $HeapSucc(a, c));

axiom (forall h: Heap, k: Heap :: 
  { $HeapSucc(h, k) } 
  $HeapSucc(h, k)
     ==> (forall o: ref :: 
      { read(k, o, alloc) } 
      $Unbox(read(h, o, alloc)) ==> $Unbox(read(k, o, alloc))));

revealed function $HeapSuccGhost(Heap, Heap) : bool;

procedure $YieldHavoc(this: ref, rds: Set, nw: Set);
  modifies $Heap;
  ensures (forall $o: ref, $f: Field :: 
    { read($Heap, $o, $f) } 
    $o != null && $Unbox(read(old($Heap), $o, alloc))
       ==> 
      $o == this || Set#IsMember(rds, $Box($o)) || Set#IsMember(nw, $Box($o))
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterHavoc0(this: ref, rds: Set, modi: Set);
  modifies $Heap;
  ensures (forall $o: ref, $f: Field :: 
    { read($Heap, $o, $f) } 
    $o != null && $Unbox(read(old($Heap), $o, alloc))
       ==> 
      Set#IsMember(rds, $Box($o)) && !Set#IsMember(modi, $Box($o)) && $o != this
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterHavoc1(this: ref, modi: Set, nw: Set);
  modifies $Heap;
  ensures (forall $o: ref, $f: Field :: 
    { read($Heap, $o, $f) } 
    $o != null && $Unbox(read(old($Heap), $o, alloc))
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || $o == this
         || Set#IsMember(modi, $Box($o))
         || Set#IsMember(nw, $Box($o)));
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterCollectNewObjects(prevHeap: Heap, newHeap: Heap, this: ref, NW: Field) returns (s: Set);
  ensures (forall bx: Box :: 
    { Set#IsMember(s, bx) } 
    Set#IsMember(s, bx)
       <==> Set#IsMember($Unbox(read(newHeap, this, NW)): Set, bx)
         || (
          $Unbox(bx) != null
           && !$Unbox(read(prevHeap, $Unbox(bx): ref, alloc))
           && $Unbox(read(newHeap, $Unbox(bx): ref, alloc))));



type Set;

revealed function Set#Card(s: Set) : int;

axiom (forall s: Set :: { Set#Card(s) } 0 <= Set#Card(s));

revealed function Set#Empty() : Set;

revealed function Set#IsMember(s: Set, o: Box) : bool;

axiom (forall o: Box :: 
  { Set#IsMember(Set#Empty(), o) } 
  !Set#IsMember(Set#Empty(), o));

axiom (forall s: Set :: 
  { Set#Card(s) } 
  (Set#Card(s) == 0 <==> s == Set#Empty())
     && (Set#Card(s) != 0
       ==> (exists x: Box :: { Set#IsMember(s, x) } Set#IsMember(s, x))));

revealed function Set#UnionOne(s: Set, o: Box) : Set;

axiom (forall a: Set, x: Box, o: Box :: 
  { Set#IsMember(Set#UnionOne(a, x), o) } 
  Set#IsMember(Set#UnionOne(a, x), o) <==> o == x || Set#IsMember(a, o));

axiom (forall a: Set, x: Box :: 
  { Set#UnionOne(a, x) } 
  Set#IsMember(Set#UnionOne(a, x), x));

axiom (forall a: Set, x: Box, y: Box :: 
  { Set#UnionOne(a, x), Set#IsMember(a, y) } 
  Set#IsMember(a, y) ==> Set#IsMember(Set#UnionOne(a, x), y));

axiom (forall a: Set, x: Box :: 
  { Set#Card(Set#UnionOne(a, x)) } 
  Set#IsMember(a, x) ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a));

axiom (forall a: Set, x: Box :: 
  { Set#Card(Set#UnionOne(a, x)) } 
  !Set#IsMember(a, x) ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a) + 1);

revealed function Set#Union(a: Set, b: Set) : Set;

axiom (forall a: Set, b: Set, o: Box :: 
  { Set#IsMember(Set#Union(a, b), o) } 
  Set#IsMember(Set#Union(a, b), o) <==> Set#IsMember(a, o) || Set#IsMember(b, o));

axiom (forall a: Set, b: Set, y: Box :: 
  { Set#Union(a, b), Set#IsMember(a, y) } 
  Set#IsMember(a, y) ==> Set#IsMember(Set#Union(a, b), y));

axiom (forall a: Set, b: Set, y: Box :: 
  { Set#Union(a, b), Set#IsMember(b, y) } 
  Set#IsMember(b, y) ==> Set#IsMember(Set#Union(a, b), y));

axiom (forall a: Set, b: Set :: 
  { Set#Union(a, b) } 
  Set#Disjoint(a, b)
     ==> Set#Difference(Set#Union(a, b), a) == b
       && Set#Difference(Set#Union(a, b), b) == a);

revealed function Set#Intersection(a: Set, b: Set) : Set;

axiom (forall a: Set, b: Set, o: Box :: 
  { Set#IsMember(Set#Intersection(a, b), o) } 
  Set#IsMember(Set#Intersection(a, b), o)
     <==> Set#IsMember(a, o) && Set#IsMember(b, o));

axiom (forall a: Set, b: Set :: 
  { Set#Union(Set#Union(a, b), b) } 
  Set#Union(Set#Union(a, b), b) == Set#Union(a, b));

axiom (forall a: Set, b: Set :: 
  { Set#Union(a, Set#Union(a, b)) } 
  Set#Union(a, Set#Union(a, b)) == Set#Union(a, b));

axiom (forall a: Set, b: Set :: 
  { Set#Intersection(Set#Intersection(a, b), b) } 
  Set#Intersection(Set#Intersection(a, b), b) == Set#Intersection(a, b));

axiom (forall a: Set, b: Set :: 
  { Set#Intersection(a, Set#Intersection(a, b)) } 
  Set#Intersection(a, Set#Intersection(a, b)) == Set#Intersection(a, b));

axiom (forall a: Set, b: Set :: 
  { Set#Card(Set#Union(a, b)) } { Set#Card(Set#Intersection(a, b)) } 
  Set#Card(Set#Union(a, b)) + Set#Card(Set#Intersection(a, b))
     == Set#Card(a) + Set#Card(b));

revealed function Set#Difference(a: Set, b: Set) : Set;

axiom (forall a: Set, b: Set, o: Box :: 
  { Set#IsMember(Set#Difference(a, b), o) } 
  Set#IsMember(Set#Difference(a, b), o)
     <==> Set#IsMember(a, o) && !Set#IsMember(b, o));

axiom (forall a: Set, b: Set, y: Box :: 
  { Set#Difference(a, b), Set#IsMember(b, y) } 
  Set#IsMember(b, y) ==> !Set#IsMember(Set#Difference(a, b), y));

axiom (forall a: Set, b: Set :: 
  { Set#Card(Set#Difference(a, b)) } 
  Set#Card(Set#Difference(a, b))
         + Set#Card(Set#Difference(b, a))
         + Set#Card(Set#Intersection(a, b))
       == Set#Card(Set#Union(a, b))
     && Set#Card(Set#Difference(a, b)) == Set#Card(a) - Set#Card(Set#Intersection(a, b)));

revealed function Set#Subset(a: Set, b: Set) : bool;

axiom (forall a: Set, b: Set :: 
  { Set#Subset(a, b) } 
  Set#Subset(a, b)
     <==> (forall o: Box :: 
      { Set#IsMember(a, o) } { Set#IsMember(b, o) } 
      Set#IsMember(a, o) ==> Set#IsMember(b, o)));

revealed function Set#Equal(a: Set, b: Set) : bool;

axiom (forall a: Set, b: Set :: 
  { Set#Equal(a, b) } 
  Set#Equal(a, b)
     <==> (forall o: Box :: 
      { Set#IsMember(a, o) } { Set#IsMember(b, o) } 
      Set#IsMember(a, o) <==> Set#IsMember(b, o)));

axiom (forall a: Set, b: Set :: { Set#Equal(a, b) } Set#Equal(a, b) ==> a == b);

revealed function Set#Disjoint(a: Set, b: Set) : bool;

axiom (forall a: Set, b: Set :: 
  { Set#Disjoint(a, b) } 
  Set#Disjoint(a, b)
     <==> (forall o: Box :: 
      { Set#IsMember(a, o) } { Set#IsMember(b, o) } 
      !Set#IsMember(a, o) || !Set#IsMember(b, o)));

revealed function Set#FromBoogieMap([Box]bool) : Set;

axiom (forall m: [Box]bool, bx: Box :: 
  { Set#IsMember(Set#FromBoogieMap(m), bx) } 
  Set#IsMember(Set#FromBoogieMap(m), bx) == m[bx]);

type ISet = [Box]bool;

revealed function ISet#Empty() : ISet;

axiom (forall o: Box :: { ISet#Empty()[o] } !ISet#Empty()[o]);

revealed function ISet#FromSet(Set) : ISet;

axiom (forall s: Set, bx: Box :: 
  { ISet#FromSet(s)[bx] } 
  ISet#FromSet(s)[bx] == Set#IsMember(s, bx));

revealed function ISet#UnionOne(ISet, Box) : ISet;

axiom (forall a: ISet, x: Box, o: Box :: 
  { ISet#UnionOne(a, x)[o] } 
  ISet#UnionOne(a, x)[o] <==> o == x || a[o]);

axiom (forall a: ISet, x: Box :: { ISet#UnionOne(a, x) } ISet#UnionOne(a, x)[x]);

axiom (forall a: ISet, x: Box, y: Box :: 
  { ISet#UnionOne(a, x), a[y] } 
  a[y] ==> ISet#UnionOne(a, x)[y]);

revealed function ISet#Union(ISet, ISet) : ISet;

axiom (forall a: ISet, b: ISet, o: Box :: 
  { ISet#Union(a, b)[o] } 
  ISet#Union(a, b)[o] <==> a[o] || b[o]);

axiom (forall a: ISet, b: ISet, y: Box :: 
  { ISet#Union(a, b), a[y] } 
  a[y] ==> ISet#Union(a, b)[y]);

axiom (forall a: ISet, b: ISet, y: Box :: 
  { ISet#Union(a, b), b[y] } 
  b[y] ==> ISet#Union(a, b)[y]);

axiom (forall a: ISet, b: ISet :: 
  { ISet#Union(a, b) } 
  ISet#Disjoint(a, b)
     ==> ISet#Difference(ISet#Union(a, b), a) == b
       && ISet#Difference(ISet#Union(a, b), b) == a);

revealed function ISet#Intersection(ISet, ISet) : ISet;

axiom (forall a: ISet, b: ISet, o: Box :: 
  { ISet#Intersection(a, b)[o] } 
  ISet#Intersection(a, b)[o] <==> a[o] && b[o]);

axiom (forall a: ISet, b: ISet :: 
  { ISet#Union(ISet#Union(a, b), b) } 
  ISet#Union(ISet#Union(a, b), b) == ISet#Union(a, b));

axiom (forall a: ISet, b: ISet :: 
  { ISet#Union(a, ISet#Union(a, b)) } 
  ISet#Union(a, ISet#Union(a, b)) == ISet#Union(a, b));

axiom (forall a: ISet, b: ISet :: 
  { ISet#Intersection(ISet#Intersection(a, b), b) } 
  ISet#Intersection(ISet#Intersection(a, b), b) == ISet#Intersection(a, b));

axiom (forall a: ISet, b: ISet :: 
  { ISet#Intersection(a, ISet#Intersection(a, b)) } 
  ISet#Intersection(a, ISet#Intersection(a, b)) == ISet#Intersection(a, b));

revealed function ISet#Difference(ISet, ISet) : ISet;

axiom (forall a: ISet, b: ISet, o: Box :: 
  { ISet#Difference(a, b)[o] } 
  ISet#Difference(a, b)[o] <==> a[o] && !b[o]);

axiom (forall a: ISet, b: ISet, y: Box :: 
  { ISet#Difference(a, b), b[y] } 
  b[y] ==> !ISet#Difference(a, b)[y]);

revealed function ISet#Subset(ISet, ISet) : bool;

axiom (forall a: ISet, b: ISet :: 
  { ISet#Subset(a, b) } 
  ISet#Subset(a, b) <==> (forall o: Box :: { a[o] } { b[o] } a[o] ==> b[o]));

revealed function ISet#Equal(ISet, ISet) : bool;

axiom (forall a: ISet, b: ISet :: 
  { ISet#Equal(a, b) } 
  ISet#Equal(a, b) <==> (forall o: Box :: { a[o] } { b[o] } a[o] <==> b[o]));

axiom (forall a: ISet, b: ISet :: { ISet#Equal(a, b) } ISet#Equal(a, b) ==> a == b);

revealed function ISet#Disjoint(ISet, ISet) : bool;

axiom (forall a: ISet, b: ISet :: 
  { ISet#Disjoint(a, b) } 
  ISet#Disjoint(a, b) <==> (forall o: Box :: { a[o] } { b[o] } !a[o] || !b[o]));

revealed function Math#min(a: int, b: int) : int;

axiom (forall a: int, b: int :: { Math#min(a, b) } a <= b <==> Math#min(a, b) == a);

axiom (forall a: int, b: int :: { Math#min(a, b) } b <= a <==> Math#min(a, b) == b);

axiom (forall a: int, b: int :: 
  { Math#min(a, b) } 
  Math#min(a, b) == a || Math#min(a, b) == b);

revealed function Math#clip(a: int) : int;

axiom (forall a: int :: { Math#clip(a) } 0 <= a ==> Math#clip(a) == a);

axiom (forall a: int :: { Math#clip(a) } a < 0 ==> Math#clip(a) == 0);

type MultiSet;

revealed function MultiSet#Multiplicity(m: MultiSet, o: Box) : int;

revealed function MultiSet#UpdateMultiplicity(m: MultiSet, o: Box, n: int) : MultiSet;

axiom (forall m: MultiSet, o: Box, n: int, p: Box :: 
  { MultiSet#Multiplicity(MultiSet#UpdateMultiplicity(m, o, n), p) } 
  0 <= n
     ==> (o == p ==> MultiSet#Multiplicity(MultiSet#UpdateMultiplicity(m, o, n), p) == n)
       && (o != p
         ==> MultiSet#Multiplicity(MultiSet#UpdateMultiplicity(m, o, n), p)
           == MultiSet#Multiplicity(m, p)));

revealed function $IsGoodMultiSet(ms: MultiSet) : bool;

axiom (forall ms: MultiSet :: 
  { $IsGoodMultiSet(ms) } 
  $IsGoodMultiSet(ms)
     <==> (forall bx: Box :: 
      { MultiSet#Multiplicity(ms, bx) } 
      0 <= MultiSet#Multiplicity(ms, bx)
         && MultiSet#Multiplicity(ms, bx) <= MultiSet#Card(ms)));

revealed function MultiSet#Card(m: MultiSet) : int;

axiom (forall s: MultiSet :: { MultiSet#Card(s) } 0 <= MultiSet#Card(s));

axiom (forall s: MultiSet, x: Box, n: int :: 
  { MultiSet#Card(MultiSet#UpdateMultiplicity(s, x, n)) } 
  0 <= n
     ==> MultiSet#Card(MultiSet#UpdateMultiplicity(s, x, n))
       == MultiSet#Card(s) - MultiSet#Multiplicity(s, x) + n);

revealed function MultiSet#Empty() : MultiSet;

axiom (forall o: Box :: 
  { MultiSet#Multiplicity(MultiSet#Empty(), o) } 
  MultiSet#Multiplicity(MultiSet#Empty(), o) == 0);

axiom (forall s: MultiSet :: 
  { MultiSet#Card(s) } 
  (MultiSet#Card(s) == 0 <==> s == MultiSet#Empty())
     && (MultiSet#Card(s) != 0
       ==> (exists x: Box :: 
        { MultiSet#Multiplicity(s, x) } 
        0 < MultiSet#Multiplicity(s, x))));

revealed function MultiSet#Singleton(o: Box) : MultiSet;

axiom (forall r: Box, o: Box :: 
  { MultiSet#Multiplicity(MultiSet#Singleton(r), o) } 
  (MultiSet#Multiplicity(MultiSet#Singleton(r), o) == 1 <==> r == o)
     && (MultiSet#Multiplicity(MultiSet#Singleton(r), o) == 0 <==> r != o));

axiom (forall r: Box :: 
  { MultiSet#Singleton(r) } 
  MultiSet#Singleton(r) == MultiSet#UnionOne(MultiSet#Empty(), r));

revealed function MultiSet#UnionOne(m: MultiSet, o: Box) : MultiSet;

axiom (forall a: MultiSet, x: Box, o: Box :: 
  { MultiSet#Multiplicity(MultiSet#UnionOne(a, x), o) } 
  0 < MultiSet#Multiplicity(MultiSet#UnionOne(a, x), o)
     <==> o == x || 0 < MultiSet#Multiplicity(a, o));

axiom (forall a: MultiSet, x: Box :: 
  { MultiSet#UnionOne(a, x) } 
  MultiSet#Multiplicity(MultiSet#UnionOne(a, x), x)
     == MultiSet#Multiplicity(a, x) + 1);

axiom (forall a: MultiSet, x: Box, y: Box :: 
  { MultiSet#UnionOne(a, x), MultiSet#Multiplicity(a, y) } 
  0 < MultiSet#Multiplicity(a, y)
     ==> 0 < MultiSet#Multiplicity(MultiSet#UnionOne(a, x), y));

axiom (forall a: MultiSet, x: Box, y: Box :: 
  { MultiSet#UnionOne(a, x), MultiSet#Multiplicity(a, y) } 
  x != y
     ==> MultiSet#Multiplicity(a, y) == MultiSet#Multiplicity(MultiSet#UnionOne(a, x), y));

axiom (forall a: MultiSet, x: Box :: 
  { MultiSet#Card(MultiSet#UnionOne(a, x)) } 
  MultiSet#Card(MultiSet#UnionOne(a, x)) == MultiSet#Card(a) + 1);

revealed function MultiSet#Union(a: MultiSet, b: MultiSet) : MultiSet;

axiom (forall a: MultiSet, b: MultiSet, o: Box :: 
  { MultiSet#Multiplicity(MultiSet#Union(a, b), o) } 
  MultiSet#Multiplicity(MultiSet#Union(a, b), o)
     == MultiSet#Multiplicity(a, o) + MultiSet#Multiplicity(b, o));

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Card(MultiSet#Union(a, b)) } 
  MultiSet#Card(MultiSet#Union(a, b)) == MultiSet#Card(a) + MultiSet#Card(b));

revealed function MultiSet#Intersection(a: MultiSet, b: MultiSet) : MultiSet;

axiom (forall a: MultiSet, b: MultiSet, o: Box :: 
  { MultiSet#Multiplicity(MultiSet#Intersection(a, b), o) } 
  MultiSet#Multiplicity(MultiSet#Intersection(a, b), o)
     == Math#min(MultiSet#Multiplicity(a, o), MultiSet#Multiplicity(b, o)));

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Intersection(MultiSet#Intersection(a, b), b) } 
  MultiSet#Intersection(MultiSet#Intersection(a, b), b)
     == MultiSet#Intersection(a, b));

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Intersection(a, MultiSet#Intersection(a, b)) } 
  MultiSet#Intersection(a, MultiSet#Intersection(a, b))
     == MultiSet#Intersection(a, b));

revealed function MultiSet#Difference(a: MultiSet, b: MultiSet) : MultiSet;

axiom (forall a: MultiSet, b: MultiSet, o: Box :: 
  { MultiSet#Multiplicity(MultiSet#Difference(a, b), o) } 
  MultiSet#Multiplicity(MultiSet#Difference(a, b), o)
     == Math#clip(MultiSet#Multiplicity(a, o) - MultiSet#Multiplicity(b, o)));

axiom (forall a: MultiSet, b: MultiSet, y: Box :: 
  { MultiSet#Difference(a, b), MultiSet#Multiplicity(b, y), MultiSet#Multiplicity(a, y) } 
  MultiSet#Multiplicity(a, y) <= MultiSet#Multiplicity(b, y)
     ==> MultiSet#Multiplicity(MultiSet#Difference(a, b), y) == 0);

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Card(MultiSet#Difference(a, b)) } 
  MultiSet#Card(MultiSet#Difference(a, b))
         + MultiSet#Card(MultiSet#Difference(b, a))
         + 2 * MultiSet#Card(MultiSet#Intersection(a, b))
       == MultiSet#Card(MultiSet#Union(a, b))
     && MultiSet#Card(MultiSet#Difference(a, b))
       == MultiSet#Card(a) - MultiSet#Card(MultiSet#Intersection(a, b)));

revealed function MultiSet#Subset(a: MultiSet, b: MultiSet) : bool;

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Subset(a, b) } 
  MultiSet#Subset(a, b)
     <==> (forall o: Box :: 
      { MultiSet#Multiplicity(a, o) } { MultiSet#Multiplicity(b, o) } 
      MultiSet#Multiplicity(a, o) <= MultiSet#Multiplicity(b, o)));

revealed function MultiSet#Equal(a: MultiSet, b: MultiSet) : bool;

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Equal(a, b) } 
  MultiSet#Equal(a, b)
     <==> (forall o: Box :: 
      { MultiSet#Multiplicity(a, o) } { MultiSet#Multiplicity(b, o) } 
      MultiSet#Multiplicity(a, o) == MultiSet#Multiplicity(b, o)));

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Equal(a, b) } 
  MultiSet#Equal(a, b) ==> a == b);

revealed function MultiSet#Disjoint(a: MultiSet, b: MultiSet) : bool;

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Disjoint(a, b) } 
  MultiSet#Disjoint(a, b)
     <==> (forall o: Box :: 
      { MultiSet#Multiplicity(a, o) } { MultiSet#Multiplicity(b, o) } 
      MultiSet#Multiplicity(a, o) == 0 || MultiSet#Multiplicity(b, o) == 0));

revealed function MultiSet#FromSet(s: Set) : MultiSet;

axiom (forall s: Set, a: Box :: 
  { MultiSet#Multiplicity(MultiSet#FromSet(s), a) } 
  (MultiSet#Multiplicity(MultiSet#FromSet(s), a) == 0 <==> !Set#IsMember(s, a))
     && (MultiSet#Multiplicity(MultiSet#FromSet(s), a) == 1 <==> Set#IsMember(s, a)));

axiom (forall s: Set :: 
  { MultiSet#Card(MultiSet#FromSet(s)) } 
  MultiSet#Card(MultiSet#FromSet(s)) == Set#Card(s));

revealed function MultiSet#FromSeq(s: Seq) : MultiSet
uses {
axiom MultiSet#FromSeq(Seq#Empty()) == MultiSet#Empty();
}

axiom (forall s: Seq :: { MultiSet#FromSeq(s) } $IsGoodMultiSet(MultiSet#FromSeq(s)));

axiom (forall s: Seq :: 
  { MultiSet#Card(MultiSet#FromSeq(s)) } 
  MultiSet#Card(MultiSet#FromSeq(s)) == Seq#Length(s));

axiom (forall s: Seq, v: Box :: 
  { MultiSet#FromSeq(Seq#Build(s, v)) } 
  MultiSet#FromSeq(Seq#Build(s, v)) == MultiSet#UnionOne(MultiSet#FromSeq(s), v));

axiom (forall a: Seq, b: Seq :: 
  { MultiSet#FromSeq(Seq#Append(a, b)) } 
  MultiSet#FromSeq(Seq#Append(a, b))
     == MultiSet#Union(MultiSet#FromSeq(a), MultiSet#FromSeq(b)));

axiom (forall s: Seq, i: int, v: Box, x: Box :: 
  { MultiSet#Multiplicity(MultiSet#FromSeq(Seq#Update(s, i, v)), x) } 
  0 <= i && i < Seq#Length(s)
     ==> MultiSet#Multiplicity(MultiSet#FromSeq(Seq#Update(s, i, v)), x)
       == MultiSet#Multiplicity(MultiSet#Union(MultiSet#Difference(MultiSet#FromSeq(s), MultiSet#Singleton(Seq#Index(s, i))), 
          MultiSet#Singleton(v)), 
        x));

axiom (forall s: Seq, x: Box :: 
  { MultiSet#Multiplicity(MultiSet#FromSeq(s), x) } 
  (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= i && i < Seq#Length(s) && x == Seq#Index(s, i))
     <==> 0 < MultiSet#Multiplicity(MultiSet#FromSeq(s), x));

type Seq;

revealed function Seq#Length(s: Seq) : int;

axiom (forall s: Seq :: { Seq#Length(s) } 0 <= Seq#Length(s));

revealed function Seq#Empty() : Seq
uses {
axiom Seq#Length(Seq#Empty()) == 0;
}

axiom (forall s: Seq :: { Seq#Length(s) } Seq#Length(s) == 0 ==> s == Seq#Empty());

revealed function Seq#Build(s: Seq, val: Box) : Seq;

revealed function Seq#Build_inv0(s: Seq) : Seq;

revealed function Seq#Build_inv1(s: Seq) : Box;

axiom (forall s: Seq, val: Box :: 
  { Seq#Build(s, val) } 
  Seq#Build_inv0(Seq#Build(s, val)) == s
     && Seq#Build_inv1(Seq#Build(s, val)) == val);

axiom (forall s: Seq, v: Box :: 
  { Seq#Build(s, v) } 
  Seq#Length(Seq#Build(s, v)) == 1 + Seq#Length(s));

axiom (forall s: Seq, i: int, v: Box :: 
  { Seq#Index(Seq#Build(s, v), i) } 
  (i == Seq#Length(s) ==> Seq#Index(Seq#Build(s, v), i) == v)
     && (i != Seq#Length(s) ==> Seq#Index(Seq#Build(s, v), i) == Seq#Index(s, i)));

axiom (forall s0: Seq, s1: Seq :: 
  { Seq#Length(Seq#Append(s0, s1)) } 
  Seq#Length(Seq#Append(s0, s1)) == Seq#Length(s0) + Seq#Length(s1));

revealed function Seq#Index(s: Seq, i: int) : Box;

axiom (forall s0: Seq, s1: Seq, n: int :: 
  { Seq#Index(Seq#Append(s0, s1), n) } 
  (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0, s1), n) == Seq#Index(s0, n))
     && (Seq#Length(s0) <= n
       ==> Seq#Index(Seq#Append(s0, s1), n) == Seq#Index(s1, n - Seq#Length(s0))));

revealed function Seq#Update(s: Seq, i: int, val: Box) : Seq;

axiom (forall s: Seq, i: int, v: Box :: 
  { Seq#Length(Seq#Update(s, i, v)) } 
  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s, i, v)) == Seq#Length(s));

axiom (forall s: Seq, i: int, v: Box, n: int :: 
  { Seq#Index(Seq#Update(s, i, v), n) } 
  0 <= n && n < Seq#Length(s)
     ==> (i == n ==> Seq#Index(Seq#Update(s, i, v), n) == v)
       && (i != n ==> Seq#Index(Seq#Update(s, i, v), n) == Seq#Index(s, n)));

revealed function Seq#Append(s0: Seq, s1: Seq) : Seq;

revealed function Seq#Contains(s: Seq, val: Box) : bool;

axiom (forall s: Seq, x: Box :: 
  { Seq#Contains(s, x) } 
  Seq#Contains(s, x)
     <==> (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

axiom (forall x: Box :: 
  { Seq#Contains(Seq#Empty(), x) } 
  !Seq#Contains(Seq#Empty(), x));

axiom (forall s0: Seq, s1: Seq, x: Box :: 
  { Seq#Contains(Seq#Append(s0, s1), x) } 
  Seq#Contains(Seq#Append(s0, s1), x)
     <==> Seq#Contains(s0, x) || Seq#Contains(s1, x));

axiom (forall s: Seq, v: Box, x: Box :: 
  { Seq#Contains(Seq#Build(s, v), x) } 
  Seq#Contains(Seq#Build(s, v), x) <==> v == x || Seq#Contains(s, x));

axiom (forall s: Seq, n: int, x: Box :: 
  { Seq#Contains(Seq#Take(s, n), x) } 
  Seq#Contains(Seq#Take(s, n), x)
     <==> (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));

axiom (forall s: Seq, n: int, x: Box :: 
  { Seq#Contains(Seq#Drop(s, n), x) } 
  Seq#Contains(Seq#Drop(s, n), x)
     <==> (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

revealed function Seq#Equal(s0: Seq, s1: Seq) : bool;

axiom (forall s0: Seq, s1: Seq :: 
  { Seq#Equal(s0, s1) } 
  Seq#Equal(s0, s1)
     <==> Seq#Length(s0) == Seq#Length(s1)
       && (forall j: int :: 
        { Seq#Index(s0, j) } { Seq#Index(s1, j) } 
        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0, j) == Seq#Index(s1, j)));

axiom (forall a: Seq, b: Seq :: { Seq#Equal(a, b) } Seq#Equal(a, b) ==> a == b);

revealed function Seq#SameUntil(s0: Seq, s1: Seq, n: int) : bool;

axiom (forall s0: Seq, s1: Seq, n: int :: 
  { Seq#SameUntil(s0, s1, n) } 
  Seq#SameUntil(s0, s1, n)
     <==> (forall j: int :: 
      { Seq#Index(s0, j) } { Seq#Index(s1, j) } 
      0 <= j && j < n ==> Seq#Index(s0, j) == Seq#Index(s1, j)));

revealed function Seq#Take(s: Seq, howMany: int) : Seq;

axiom (forall s: Seq, n: int :: 
  { Seq#Length(Seq#Take(s, n)) } 
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s, n)) == n);

axiom (forall s: Seq, n: int, j: int :: 
  {:weight 11} { Seq#Index(Seq#Take(s, n), j) } { Seq#Index(s, j), Seq#Take(s, n) } 
  0 <= j && j < n && j < Seq#Length(s)
     ==> Seq#Index(Seq#Take(s, n), j) == Seq#Index(s, j));

revealed function Seq#Drop(s: Seq, howMany: int) : Seq;

axiom (forall s: Seq, n: int :: 
  { Seq#Length(Seq#Drop(s, n)) } 
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s, n)) == Seq#Length(s) - n);

axiom (forall s: Seq, n: int, j: int :: 
  {:weight 11} { Seq#Index(Seq#Drop(s, n), j) } 
  0 <= n && 0 <= j && j < Seq#Length(s) - n
     ==> Seq#Index(Seq#Drop(s, n), j) == Seq#Index(s, j + n));

axiom (forall s: Seq, n: int, k: int :: 
  {:weight 11} { Seq#Index(s, k), Seq#Drop(s, n) } 
  0 <= n && n <= k && k < Seq#Length(s)
     ==> Seq#Index(Seq#Drop(s, n), k - n) == Seq#Index(s, k));

axiom (forall s: Seq, t: Seq, n: int :: 
  { Seq#Take(Seq#Append(s, t), n) } { Seq#Drop(Seq#Append(s, t), n) } 
  n == Seq#Length(s)
     ==> Seq#Take(Seq#Append(s, t), n) == s && Seq#Drop(Seq#Append(s, t), n) == t);

axiom (forall s: Seq, i: int, v: Box, n: int :: 
  { Seq#Take(Seq#Update(s, i, v), n) } 
  0 <= i && i < n && n <= Seq#Length(s)
     ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v));

axiom (forall s: Seq, i: int, v: Box, n: int :: 
  { Seq#Take(Seq#Update(s, i, v), n) } 
  n <= i && i < Seq#Length(s)
     ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));

axiom (forall s: Seq, i: int, v: Box, n: int :: 
  { Seq#Drop(Seq#Update(s, i, v), n) } 
  0 <= n && n <= i && i < Seq#Length(s)
     ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i - n, v));

axiom (forall s: Seq, i: int, v: Box, n: int :: 
  { Seq#Drop(Seq#Update(s, i, v), n) } 
  0 <= i && i < n && n <= Seq#Length(s)
     ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));

axiom (forall s: Seq, v: Box, n: int :: 
  { Seq#Drop(Seq#Build(s, v), n) } 
  0 <= n && n <= Seq#Length(s)
     ==> Seq#Drop(Seq#Build(s, v), n) == Seq#Build(Seq#Drop(s, n), v));

axiom (forall s: Seq, n: int :: { Seq#Drop(s, n) } n == 0 ==> Seq#Drop(s, n) == s);

axiom (forall s: Seq, n: int :: 
  { Seq#Take(s, n) } 
  n == 0 ==> Seq#Take(s, n) == Seq#Empty());

axiom (forall s: Seq, m: int, n: int :: 
  { Seq#Drop(Seq#Drop(s, m), n) } 
  0 <= m && 0 <= n && m + n <= Seq#Length(s)
     ==> Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, m + n));

axiom (forall s: Seq, bx: Box, t: Ty :: 
  { $Is(Seq#Build(s, bx), TSeq(t)) } 
  $Is(s, TSeq(t)) && $IsBox(bx, t) ==> $Is(Seq#Build(s, bx), TSeq(t)));

revealed function Seq#Create(ty: Ty, heap: Heap, len: int, init: HandleType) : Seq;

axiom (forall ty: Ty, heap: Heap, len: int, init: HandleType :: 
  { Seq#Length(Seq#Create(ty, heap, len, init): Seq) } 
  $IsGoodHeap(heap) && 0 <= len
     ==> Seq#Length(Seq#Create(ty, heap, len, init): Seq) == len);

axiom (forall ty: Ty, heap: Heap, len: int, init: HandleType, i: int :: 
  { Seq#Index(Seq#Create(ty, heap, len, init), i) } 
  $IsGoodHeap(heap) && 0 <= i && i < len
     ==> Seq#Index(Seq#Create(ty, heap, len, init), i)
       == Apply1(TInt, ty, heap, init, $Box(i)));

revealed function Seq#FromArray(h: Heap, a: ref) : Seq;

axiom (forall h: Heap, a: ref :: 
  { Seq#Length(Seq#FromArray(h, a)) } 
  Seq#Length(Seq#FromArray(h, a)) == _System.array.Length(a));

axiom (forall h: Heap, a: ref :: 
  { Seq#FromArray(h, a) } 
  (forall i: int :: 
    { read(h, a, IndexField(i)) } { Seq#Index(Seq#FromArray(h, a): Seq, i) } 
    0 <= i && i < Seq#Length(Seq#FromArray(h, a))
       ==> Seq#Index(Seq#FromArray(h, a), i) == read(h, a, IndexField(i))));

axiom (forall h0: Heap, h1: Heap, a: ref :: 
  { Seq#FromArray(h1, a), $HeapSucc(h0, h1) } 
  $IsGoodHeap(h0) && $IsGoodHeap(h1) && $HeapSucc(h0, h1) && h0[a] == h1[a]
     ==> Seq#FromArray(h0, a) == Seq#FromArray(h1, a));

axiom (forall h: Heap, i: int, v: Box, a: ref :: 
  { Seq#FromArray(update(h, a, IndexField(i), v), a) } 
  0 <= i && i < _System.array.Length(a)
     ==> Seq#FromArray(update(h, a, IndexField(i), v), a)
       == Seq#Update(Seq#FromArray(h, a), i, v));

axiom (forall h: Heap, a: ref, n0: int, n1: int :: 
  { Seq#Take(Seq#FromArray(h, a), n0), Seq#Take(Seq#FromArray(h, a), n1) } 
  n0 + 1 == n1 && 0 <= n0 && n1 <= _System.array.Length(a)
     ==> Seq#Take(Seq#FromArray(h, a), n1)
       == Seq#Build(Seq#Take(Seq#FromArray(h, a), n0), read(h, a, IndexField(n0): Field)));

revealed function Seq#Rank(Seq) : int;

axiom (forall s: Seq, i: int :: 
  { DtRank($Unbox(Seq#Index(s, i)): DatatypeType) } 
  0 <= i && i < Seq#Length(s)
     ==> DtRank($Unbox(Seq#Index(s, i)): DatatypeType) < Seq#Rank(s));

axiom (forall s: Seq, i: int :: 
  { Seq#Rank(Seq#Drop(s, i)) } 
  0 < i && i <= Seq#Length(s) ==> Seq#Rank(Seq#Drop(s, i)) < Seq#Rank(s));

axiom (forall s: Seq, i: int :: 
  { Seq#Rank(Seq#Take(s, i)) } 
  0 <= i && i < Seq#Length(s) ==> Seq#Rank(Seq#Take(s, i)) < Seq#Rank(s));

axiom (forall s: Seq, i: int, j: int :: 
  { Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) } 
  0 <= i && i < j && j <= Seq#Length(s)
     ==> Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) < Seq#Rank(s));

type Map;

revealed function Map#Domain(Map) : Set;

revealed function Map#Elements(Map) : [Box]Box;

revealed function Map#Card(Map) : int;

axiom (forall m: Map :: { Map#Card(m) } 0 <= Map#Card(m));

axiom (forall m: Map :: { Map#Card(m) } Map#Card(m) == 0 <==> m == Map#Empty());

axiom (forall m: Map :: 
  { Map#Domain(m) } 
  m == Map#Empty() || (exists k: Box :: Set#IsMember(Map#Domain(m), k)));

axiom (forall m: Map :: 
  { Map#Values(m) } 
  m == Map#Empty() || (exists v: Box :: Set#IsMember(Map#Values(m), v)));

axiom (forall m: Map :: 
  { Map#Items(m) } 
  m == Map#Empty()
     || (exists k: Box, v: Box :: 
      Set#IsMember(Map#Items(m), $Box(#_System._tuple#2._#Make2(k, v)))));

axiom (forall m: Map :: 
  { Set#Card(Map#Domain(m)) } { Map#Card(m) } 
  Set#Card(Map#Domain(m)) == Map#Card(m));

axiom (forall m: Map :: 
  { Set#Card(Map#Values(m)) } { Map#Card(m) } 
  Set#Card(Map#Values(m)) <= Map#Card(m));

axiom (forall m: Map :: 
  { Set#Card(Map#Items(m)) } { Map#Card(m) } 
  Set#Card(Map#Items(m)) == Map#Card(m));

revealed function Map#Values(Map) : Set;

axiom (forall m: Map, v: Box :: 
  { Set#IsMember(Map#Values(m), v) } 
  Set#IsMember(Map#Values(m), v)
     == (exists u: Box :: 
      { Set#IsMember(Map#Domain(m), u) } { Map#Elements(m)[u] } 
      Set#IsMember(Map#Domain(m), u) && v == Map#Elements(m)[u]));

revealed function Map#Items(Map) : Set;

revealed function #_System._tuple#2._#Make2(Box, Box) : DatatypeType;

revealed function _System.Tuple2._0(DatatypeType) : Box;

revealed function _System.Tuple2._1(DatatypeType) : Box;

axiom (forall m: Map, item: Box :: 
  { Set#IsMember(Map#Items(m), item) } 
  Set#IsMember(Map#Items(m), item)
     <==> Set#IsMember(Map#Domain(m), _System.Tuple2._0($Unbox(item)))
       && Map#Elements(m)[_System.Tuple2._0($Unbox(item))]
         == _System.Tuple2._1($Unbox(item)));

revealed function Map#Empty() : Map;

axiom (forall u: Box :: 
  { Set#IsMember(Map#Domain(Map#Empty(): Map), u) } 
  !Set#IsMember(Map#Domain(Map#Empty(): Map), u));

revealed function Map#Glue(Set, [Box]Box, Ty) : Map;

axiom (forall a: Set, b: [Box]Box, t: Ty :: 
  { Map#Domain(Map#Glue(a, b, t)) } 
  Map#Domain(Map#Glue(a, b, t)) == a);

axiom (forall a: Set, b: [Box]Box, t: Ty :: 
  { Map#Elements(Map#Glue(a, b, t)) } 
  Map#Elements(Map#Glue(a, b, t)) == b);

axiom (forall a: Set, b: [Box]Box, t0: Ty, t1: Ty :: 
  { Map#Glue(a, b, TMap(t0, t1)) } 
  (forall bx: Box :: Set#IsMember(a, bx) ==> $IsBox(bx, t0) && $IsBox(b[bx], t1))
     ==> $Is(Map#Glue(a, b, TMap(t0, t1)), TMap(t0, t1)));

revealed function Map#Build(Map, Box, Box) : Map;

axiom (forall m: Map, u: Box, u': Box, v: Box :: 
  { Set#IsMember(Map#Domain(Map#Build(m, u, v)), u') } 
    { Map#Elements(Map#Build(m, u, v))[u'] } 
  (u' == u
       ==> Set#IsMember(Map#Domain(Map#Build(m, u, v)), u')
         && Map#Elements(Map#Build(m, u, v))[u'] == v)
     && (u' != u
       ==> Set#IsMember(Map#Domain(Map#Build(m, u, v)), u')
           == Set#IsMember(Map#Domain(m), u')
         && Map#Elements(Map#Build(m, u, v))[u'] == Map#Elements(m)[u']));

axiom (forall m: Map, u: Box, v: Box :: 
  { Map#Card(Map#Build(m, u, v)) } 
  Set#IsMember(Map#Domain(m), u) ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m));

axiom (forall m: Map, u: Box, v: Box :: 
  { Map#Card(Map#Build(m, u, v)) } 
  !Set#IsMember(Map#Domain(m), u)
     ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m) + 1);

revealed function Map#Merge(Map, Map) : Map;

axiom (forall m: Map, n: Map :: 
  { Map#Domain(Map#Merge(m, n)) } 
  Map#Domain(Map#Merge(m, n)) == Set#Union(Map#Domain(m), Map#Domain(n)));

axiom (forall m: Map, n: Map, u: Box :: 
  { Map#Elements(Map#Merge(m, n))[u] } 
  Set#IsMember(Map#Domain(Map#Merge(m, n)), u)
     ==> (!Set#IsMember(Map#Domain(n), u)
         ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(m)[u])
       && (Set#IsMember(Map#Domain(n), u)
         ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(n)[u]));

revealed function Map#Subtract(Map, Set) : Map;

axiom (forall m: Map, s: Set :: 
  { Map#Domain(Map#Subtract(m, s)) } 
  Map#Domain(Map#Subtract(m, s)) == Set#Difference(Map#Domain(m), s));

axiom (forall m: Map, s: Set, u: Box :: 
  { Map#Elements(Map#Subtract(m, s))[u] } 
  Set#IsMember(Map#Domain(Map#Subtract(m, s)), u)
     ==> Map#Elements(Map#Subtract(m, s))[u] == Map#Elements(m)[u]);

revealed function Map#Equal(Map, Map) : bool;

axiom (forall m: Map, m': Map :: 
  { Map#Equal(m, m') } 
  Map#Equal(m, m')
     <==> (forall u: Box :: 
        Set#IsMember(Map#Domain(m), u) == Set#IsMember(Map#Domain(m'), u))
       && (forall u: Box :: 
        Set#IsMember(Map#Domain(m), u) ==> Map#Elements(m)[u] == Map#Elements(m')[u]));

axiom (forall m: Map, m': Map :: { Map#Equal(m, m') } Map#Equal(m, m') ==> m == m');

revealed function Map#Disjoint(Map, Map) : bool;

axiom (forall m: Map, m': Map :: 
  { Map#Disjoint(m, m') } 
  Map#Disjoint(m, m')
     <==> (forall o: Box :: 
      { Set#IsMember(Map#Domain(m), o) } { Set#IsMember(Map#Domain(m'), o) } 
      !Set#IsMember(Map#Domain(m), o) || !Set#IsMember(Map#Domain(m'), o)));

type IMap;

revealed function IMap#Domain(IMap) : ISet;

revealed function IMap#Elements(IMap) : [Box]Box;

axiom (forall m: IMap :: 
  { IMap#Domain(m) } 
  m == IMap#Empty() || (exists k: Box :: IMap#Domain(m)[k]));

axiom (forall m: IMap :: 
  { IMap#Values(m) } 
  m == IMap#Empty() || (exists v: Box :: IMap#Values(m)[v]));

axiom (forall m: IMap :: 
  { IMap#Items(m) } 
  m == IMap#Empty()
     || (exists k: Box, v: Box :: IMap#Items(m)[$Box(#_System._tuple#2._#Make2(k, v))]));

axiom (forall m: IMap :: 
  { IMap#Domain(m) } 
  m == IMap#Empty() <==> IMap#Domain(m) == ISet#Empty());

axiom (forall m: IMap :: 
  { IMap#Values(m) } 
  m == IMap#Empty() <==> IMap#Values(m) == ISet#Empty());

axiom (forall m: IMap :: 
  { IMap#Items(m) } 
  m == IMap#Empty() <==> IMap#Items(m) == ISet#Empty());

revealed function IMap#Values(IMap) : ISet;

axiom (forall m: IMap, v: Box :: 
  { IMap#Values(m)[v] } 
  IMap#Values(m)[v]
     == (exists u: Box :: 
      { IMap#Domain(m)[u] } { IMap#Elements(m)[u] } 
      IMap#Domain(m)[u] && v == IMap#Elements(m)[u]));

revealed function IMap#Items(IMap) : ISet;

axiom (forall m: IMap, item: Box :: 
  { IMap#Items(m)[item] } 
  IMap#Items(m)[item]
     <==> IMap#Domain(m)[_System.Tuple2._0($Unbox(item))]
       && IMap#Elements(m)[_System.Tuple2._0($Unbox(item))]
         == _System.Tuple2._1($Unbox(item)));

revealed function IMap#Empty() : IMap;

axiom (forall u: Box :: 
  { IMap#Domain(IMap#Empty(): IMap)[u] } 
  !IMap#Domain(IMap#Empty(): IMap)[u]);

revealed function IMap#Glue([Box]bool, [Box]Box, Ty) : IMap;

axiom (forall a: [Box]bool, b: [Box]Box, t: Ty :: 
  { IMap#Domain(IMap#Glue(a, b, t)) } 
  IMap#Domain(IMap#Glue(a, b, t)) == a);

axiom (forall a: [Box]bool, b: [Box]Box, t: Ty :: 
  { IMap#Elements(IMap#Glue(a, b, t)) } 
  IMap#Elements(IMap#Glue(a, b, t)) == b);

axiom (forall a: [Box]bool, b: [Box]Box, t0: Ty, t1: Ty :: 
  { IMap#Glue(a, b, TIMap(t0, t1)) } 
  (forall bx: Box :: a[bx] ==> $IsBox(bx, t0) && $IsBox(b[bx], t1))
     ==> $Is(IMap#Glue(a, b, TIMap(t0, t1)), TIMap(t0, t1)));

revealed function IMap#Build(IMap, Box, Box) : IMap;

axiom (forall m: IMap, u: Box, u': Box, v: Box :: 
  { IMap#Domain(IMap#Build(m, u, v))[u'] } 
    { IMap#Elements(IMap#Build(m, u, v))[u'] } 
  (u' == u
       ==> IMap#Domain(IMap#Build(m, u, v))[u']
         && IMap#Elements(IMap#Build(m, u, v))[u'] == v)
     && (u' != u
       ==> IMap#Domain(IMap#Build(m, u, v))[u'] == IMap#Domain(m)[u']
         && IMap#Elements(IMap#Build(m, u, v))[u'] == IMap#Elements(m)[u']));

revealed function IMap#Equal(IMap, IMap) : bool;

axiom (forall m: IMap, m': IMap :: 
  { IMap#Equal(m, m') } 
  IMap#Equal(m, m')
     <==> (forall u: Box :: IMap#Domain(m)[u] == IMap#Domain(m')[u])
       && (forall u: Box :: 
        IMap#Domain(m)[u] ==> IMap#Elements(m)[u] == IMap#Elements(m')[u]));

axiom (forall m: IMap, m': IMap :: 
  { IMap#Equal(m, m') } 
  IMap#Equal(m, m') ==> m == m');

revealed function IMap#Merge(IMap, IMap) : IMap;

axiom (forall m: IMap, n: IMap :: 
  { IMap#Domain(IMap#Merge(m, n)) } 
  IMap#Domain(IMap#Merge(m, n)) == ISet#Union(IMap#Domain(m), IMap#Domain(n)));

axiom (forall m: IMap, n: IMap, u: Box :: 
  { IMap#Elements(IMap#Merge(m, n))[u] } 
  IMap#Domain(IMap#Merge(m, n))[u]
     ==> (!IMap#Domain(n)[u]
         ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(m)[u])
       && (IMap#Domain(n)[u]
         ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(n)[u]));

revealed function IMap#Subtract(IMap, Set) : IMap;

axiom (forall m: IMap, s: Set :: 
  { IMap#Domain(IMap#Subtract(m, s)) } 
  IMap#Domain(IMap#Subtract(m, s))
     == ISet#Difference(IMap#Domain(m), ISet#FromSet(s)));

axiom (forall m: IMap, s: Set, u: Box :: 
  { IMap#Elements(IMap#Subtract(m, s))[u] } 
  IMap#Domain(IMap#Subtract(m, s))[u]
     ==> IMap#Elements(IMap#Subtract(m, s))[u] == IMap#Elements(m)[u]);

revealed function INTERNAL_add_boogie(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: 
  { INTERNAL_add_boogie(x, y): int } 
  INTERNAL_add_boogie(x, y): int == x + y);
}

revealed function INTERNAL_sub_boogie(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: 
  { INTERNAL_sub_boogie(x, y): int } 
  INTERNAL_sub_boogie(x, y): int == x - y);
}

revealed function INTERNAL_mul_boogie(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: 
  { INTERNAL_mul_boogie(x, y): int } 
  INTERNAL_mul_boogie(x, y): int == x * y);
}

revealed function INTERNAL_div_boogie(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: 
  { INTERNAL_div_boogie(x, y): int } 
  INTERNAL_div_boogie(x, y): int == x div y);
}

revealed function INTERNAL_mod_boogie(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: 
  { INTERNAL_mod_boogie(x, y): int } 
  INTERNAL_mod_boogie(x, y): int == x mod y);
}

revealed function {:never_pattern true} INTERNAL_lt_boogie(x: int, y: int) : bool
uses {
axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_lt_boogie(x, y): bool } 
  INTERNAL_lt_boogie(x, y): bool == (x < y));
}

revealed function {:never_pattern true} INTERNAL_le_boogie(x: int, y: int) : bool
uses {
axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_le_boogie(x, y): bool } 
  INTERNAL_le_boogie(x, y): bool == (x <= y));
}

revealed function {:never_pattern true} INTERNAL_gt_boogie(x: int, y: int) : bool
uses {
axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_gt_boogie(x, y): bool } 
  INTERNAL_gt_boogie(x, y): bool == (x > y));
}

revealed function {:never_pattern true} INTERNAL_ge_boogie(x: int, y: int) : bool
uses {
axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_ge_boogie(x, y): bool } 
  INTERNAL_ge_boogie(x, y): bool == (x >= y));
}

revealed function Mul(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: { Mul(x, y): int } Mul(x, y): int == x * y);
}

revealed function Div(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: { Div(x, y): int } Div(x, y): int == x div y);
}

revealed function Mod(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: { Mod(x, y): int } Mod(x, y): int == x mod y);
}

revealed function Add(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: { Add(x, y): int } Add(x, y): int == x + y);
}

revealed function Sub(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: { Sub(x, y): int } Sub(x, y): int == x - y);
}

function Tclass._System.nat() : Ty
uses {
// Tclass._System.nat Tag
axiom Tag(Tclass._System.nat()) == Tagclass._System.nat
   && TagFamily(Tclass._System.nat()) == tytagFamily$nat;
}

const unique Tagclass._System.nat: TyTag;

// Box/unbox axiom for Tclass._System.nat
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.nat()) } 
  $IsBox(bx, Tclass._System.nat())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._System.nat()));

// $Is axiom for subset type _System.nat
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._System.nat()) } 
  $Is(x#0, Tclass._System.nat()) <==> LitInt(0) <= x#0);

// $IsAlloc axiom for subset type _System.nat
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._System.nat(), $h) } 
  $IsAlloc(x#0, Tclass._System.nat(), $h));

const unique class._System.object?: ClassName;

const unique Tagclass._System.object?: TyTag;

// Box/unbox axiom for Tclass._System.object?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.object?()) } 
  $IsBox(bx, Tclass._System.object?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._System.object?()));

// $Is axiom for trait object
axiom (forall $o: ref :: 
  { $Is($o, Tclass._System.object?()) } 
  $Is($o, Tclass._System.object?()));

// $IsAlloc axiom for trait object
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._System.object?(), $h) } 
  $IsAlloc($o, Tclass._System.object?(), $h)
     <==> $o == null || $Unbox(read($h, $o, alloc)): bool);

function implements$_System.object(ty: Ty) : bool;

function Tclass._System.object() : Ty
uses {
// Tclass._System.object Tag
axiom Tag(Tclass._System.object()) == Tagclass._System.object
   && TagFamily(Tclass._System.object()) == tytagFamily$object;
}

const unique Tagclass._System.object: TyTag;

// Box/unbox axiom for Tclass._System.object
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.object()) } 
  $IsBox(bx, Tclass._System.object())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._System.object()));

// $Is axiom for non-null type _System.object
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._System.object()) } { $Is(c#0, Tclass._System.object?()) } 
  $Is(c#0, Tclass._System.object())
     <==> $Is(c#0, Tclass._System.object?()) && c#0 != null);

// $IsAlloc axiom for non-null type _System.object
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._System.object(), $h) } 
  $IsAlloc(c#0, Tclass._System.object(), $h)
     <==> $IsAlloc(c#0, Tclass._System.object?(), $h));

const unique class._System.array?: ClassName;

function Tclass._System.array?(Ty) : Ty;

const unique Tagclass._System.array?: TyTag;

// Tclass._System.array? Tag
axiom (forall _System.array$arg: Ty :: 
  { Tclass._System.array?(_System.array$arg) } 
  Tag(Tclass._System.array?(_System.array$arg)) == Tagclass._System.array?
     && TagFamily(Tclass._System.array?(_System.array$arg)) == tytagFamily$array);

function Tclass._System.array?_0(Ty) : Ty;

// Tclass._System.array? injectivity 0
axiom (forall _System.array$arg: Ty :: 
  { Tclass._System.array?(_System.array$arg) } 
  Tclass._System.array?_0(Tclass._System.array?(_System.array$arg))
     == _System.array$arg);

// Box/unbox axiom for Tclass._System.array?
axiom (forall _System.array$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array?(_System.array$arg)) } 
  $IsBox(bx, Tclass._System.array?(_System.array$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array?(_System.array$arg)));

// array.: Type axiom
axiom (forall _System.array$arg: Ty, $h: Heap, $o: ref, $i0: int :: 
  { read($h, $o, IndexField($i0)), Tclass._System.array?(_System.array$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array?(_System.array$arg)
       && 
      0 <= $i0
       && $i0 < _System.array.Length($o)
     ==> $IsBox(read($h, $o, IndexField($i0)), _System.array$arg));

// array.: Allocation axiom
axiom (forall _System.array$arg: Ty, $h: Heap, $o: ref, $i0: int :: 
  { read($h, $o, IndexField($i0)), Tclass._System.array?(_System.array$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array?(_System.array$arg)
       && 
      0 <= $i0
       && $i0 < _System.array.Length($o)
       && $Unbox(read($h, $o, alloc)): bool
     ==> $IsAllocBox(read($h, $o, IndexField($i0)), _System.array$arg, $h));

// $Is axiom for array type array
axiom (forall _System.array$arg: Ty, $o: ref :: 
  { $Is($o, Tclass._System.array?(_System.array$arg)) } 
  $Is($o, Tclass._System.array?(_System.array$arg))
     <==> $o == null || dtype($o) == Tclass._System.array?(_System.array$arg));

// $IsAlloc axiom for array type array
axiom (forall _System.array$arg: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._System.array?(_System.array$arg), $h) } 
  $IsAlloc($o, Tclass._System.array?(_System.array$arg), $h)
     <==> $o == null || $Unbox(read($h, $o, alloc)): bool);

// array.Length: Type axiom
axiom (forall _System.array$arg: Ty, $o: ref :: 
  { _System.array.Length($o), Tclass._System.array?(_System.array$arg) } 
  $o != null && dtype($o) == Tclass._System.array?(_System.array$arg)
     ==> $Is(_System.array.Length($o), TInt));

// array.Length: Allocation axiom
axiom (forall _System.array$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array.Length($o), $Unbox(read($h, $o, alloc)): bool, Tclass._System.array?(_System.array$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array?(_System.array$arg)
       && $Unbox(read($h, $o, alloc)): bool
     ==> $IsAlloc(_System.array.Length($o), TInt, $h));

function Tclass._System.array(Ty) : Ty;

const unique Tagclass._System.array: TyTag;

// Tclass._System.array Tag
axiom (forall _System.array$arg: Ty :: 
  { Tclass._System.array(_System.array$arg) } 
  Tag(Tclass._System.array(_System.array$arg)) == Tagclass._System.array
     && TagFamily(Tclass._System.array(_System.array$arg)) == tytagFamily$array);

function Tclass._System.array_0(Ty) : Ty;

// Tclass._System.array injectivity 0
axiom (forall _System.array$arg: Ty :: 
  { Tclass._System.array(_System.array$arg) } 
  Tclass._System.array_0(Tclass._System.array(_System.array$arg))
     == _System.array$arg);

// Box/unbox axiom for Tclass._System.array
axiom (forall _System.array$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array(_System.array$arg)) } 
  $IsBox(bx, Tclass._System.array(_System.array$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array(_System.array$arg)));

// $Is axiom for non-null type _System.array
axiom (forall _System.array$arg: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._System.array(_System.array$arg)) } 
    { $Is(c#0, Tclass._System.array?(_System.array$arg)) } 
  $Is(c#0, Tclass._System.array(_System.array$arg))
     <==> $Is(c#0, Tclass._System.array?(_System.array$arg)) && c#0 != null);

// $IsAlloc axiom for non-null type _System.array
axiom (forall _System.array$arg: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._System.array(_System.array$arg), $h) } 
  $IsAlloc(c#0, Tclass._System.array(_System.array$arg), $h)
     <==> $IsAlloc(c#0, Tclass._System.array?(_System.array$arg), $h));

function Tclass._System.___hFunc1(Ty, Ty) : Ty;

const unique Tagclass._System.___hFunc1: TyTag;

// Tclass._System.___hFunc1 Tag
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc1(#$T0, #$R) } 
  Tag(Tclass._System.___hFunc1(#$T0, #$R)) == Tagclass._System.___hFunc1
     && TagFamily(Tclass._System.___hFunc1(#$T0, #$R)) == tytagFamily$_#Func1);

function Tclass._System.___hFunc1_0(Ty) : Ty;

// Tclass._System.___hFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc1(#$T0, #$R) } 
  Tclass._System.___hFunc1_0(Tclass._System.___hFunc1(#$T0, #$R)) == #$T0);

function Tclass._System.___hFunc1_1(Ty) : Ty;

// Tclass._System.___hFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc1(#$T0, #$R) } 
  Tclass._System.___hFunc1_1(Tclass._System.___hFunc1(#$T0, #$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hFunc1(#$T0, #$R)) } 
  $IsBox(bx, Tclass._System.___hFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc1(#$T0, #$R)));

function Handle1([Heap,Box]Box, [Heap,Box]bool, [Heap,Box]Set) : HandleType;

function Requires1(Ty, Ty, Heap, HandleType, Box) : bool;

function Reads1(Ty, Ty, Heap, HandleType, Box) : Set;

axiom (forall t0: Ty, 
    t1: Ty, 
    heap: Heap, 
    h: [Heap,Box]Box, 
    r: [Heap,Box]bool, 
    rd: [Heap,Box]Set, 
    bx0: Box :: 
  { Apply1(t0, t1, heap, Handle1(h, r, rd), bx0) } 
  Apply1(t0, t1, heap, Handle1(h, r, rd), bx0) == h[heap, bx0]);

axiom (forall t0: Ty, 
    t1: Ty, 
    heap: Heap, 
    h: [Heap,Box]Box, 
    r: [Heap,Box]bool, 
    rd: [Heap,Box]Set, 
    bx0: Box :: 
  { Requires1(t0, t1, heap, Handle1(h, r, rd), bx0) } 
  r[heap, bx0] ==> Requires1(t0, t1, heap, Handle1(h, r, rd), bx0));

axiom (forall t0: Ty, 
    t1: Ty, 
    heap: Heap, 
    h: [Heap,Box]Box, 
    r: [Heap,Box]bool, 
    rd: [Heap,Box]Set, 
    bx0: Box, 
    bx: Box :: 
  { Set#IsMember(Reads1(t0, t1, heap, Handle1(h, r, rd), bx0), bx) } 
  Set#IsMember(Reads1(t0, t1, heap, Handle1(h, r, rd), bx0), bx)
     == Set#IsMember(rd[heap, bx0], bx));

function {:inline} Requires1#canCall(t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box) : bool
{
  true
}

function {:inline} Reads1#canCall(t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box) : bool
{
  true
}

// frame axiom for Reads1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Reads1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads1(t0, t1, h0, f, bx0), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads1(t0, t1, h0, f, bx0) == Reads1(t0, t1, h1, f, bx0));

// frame axiom for Reads1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Reads1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads1(t0, t1, h1, f, bx0), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads1(t0, t1, h0, f, bx0) == Reads1(t0, t1, h1, f, bx0));

// frame axiom for Requires1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Requires1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads1(t0, t1, h0, f, bx0), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires1(t0, t1, h0, f, bx0) == Requires1(t0, t1, h1, f, bx0));

// frame axiom for Requires1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Requires1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads1(t0, t1, h1, f, bx0), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires1(t0, t1, h0, f, bx0) == Requires1(t0, t1, h1, f, bx0));

// frame axiom for Apply1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Apply1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads1(t0, t1, h0, f, bx0), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply1(t0, t1, h0, f, bx0) == Apply1(t0, t1, h1, f, bx0));

// frame axiom for Apply1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Apply1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads1(t0, t1, h1, f, bx0), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply1(t0, t1, h0, f, bx0) == Apply1(t0, t1, h1, f, bx0));

// empty-reads property for Reads1 
axiom (forall t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box :: 
  { Reads1(t0, t1, $OneHeap, f, bx0), $IsGoodHeap(heap) } 
    { Reads1(t0, t1, heap, f, bx0) } 
  $IsGoodHeap(heap) && $IsBox(bx0, t0) && $Is(f, Tclass._System.___hFunc1(t0, t1))
     ==> (Set#Equal(Reads1(t0, t1, $OneHeap, f, bx0), Set#Empty(): Set)
       <==> Set#Equal(Reads1(t0, t1, heap, f, bx0), Set#Empty(): Set)));

// empty-reads property for Requires1
axiom (forall t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box :: 
  { Requires1(t0, t1, $OneHeap, f, bx0), $IsGoodHeap(heap) } 
    { Requires1(t0, t1, heap, f, bx0) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && Set#Equal(Reads1(t0, t1, $OneHeap, f, bx0), Set#Empty(): Set)
     ==> Requires1(t0, t1, $OneHeap, f, bx0) == Requires1(t0, t1, heap, f, bx0));

axiom (forall f: HandleType, t0: Ty, t1: Ty :: 
  { $Is(f, Tclass._System.___hFunc1(t0, t1)) } 
  $Is(f, Tclass._System.___hFunc1(t0, t1))
     <==> (forall h: Heap, bx0: Box :: 
      { Apply1(t0, t1, h, f, bx0) } 
      $IsGoodHeap(h) && $IsBox(bx0, t0) && Requires1(t0, t1, h, f, bx0)
         ==> $IsBox(Apply1(t0, t1, h, f, bx0), t1)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, u0: Ty, u1: Ty :: 
  { $Is(f, Tclass._System.___hFunc1(t0, t1)), $Is(f, Tclass._System.___hFunc1(u0, u1)) } 
  $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall bx: Box :: 
        { $IsBox(bx, u0) } { $IsBox(bx, t0) } 
        $IsBox(bx, u0) ==> $IsBox(bx, t0))
       && (forall bx: Box :: 
        { $IsBox(bx, t1) } { $IsBox(bx, u1) } 
        $IsBox(bx, t1) ==> $IsBox(bx, u1))
     ==> $Is(f, Tclass._System.___hFunc1(u0, u1)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h)
       <==> (forall bx0: Box :: 
        { Apply1(t0, t1, h, f, bx0) } { Reads1(t0, t1, h, f, bx0) } 
        $IsBox(bx0, t0) && $IsAllocBox(bx0, t0, h) && Requires1(t0, t1, h, f, bx0)
           ==> (forall r: ref :: 
            { Set#IsMember(Reads1(t0, t1, h, f, bx0), $Box(r)) } 
            r != null && Set#IsMember(Reads1(t0, t1, h, f, bx0), $Box(r))
               ==> $Unbox(read(h, r, alloc)): bool))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h) } 
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h)
     ==> (forall bx0: Box :: 
      { Apply1(t0, t1, h, f, bx0) } 
      $IsAllocBox(bx0, t0, h) && Requires1(t0, t1, h, f, bx0)
         ==> $IsAllocBox(Apply1(t0, t1, h, f, bx0), t1, h)));

function Tclass._System.___hPartialFunc1(Ty, Ty) : Ty;

const unique Tagclass._System.___hPartialFunc1: TyTag;

// Tclass._System.___hPartialFunc1 Tag
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc1(#$T0, #$R) } 
  Tag(Tclass._System.___hPartialFunc1(#$T0, #$R))
       == Tagclass._System.___hPartialFunc1
     && TagFamily(Tclass._System.___hPartialFunc1(#$T0, #$R))
       == tytagFamily$_#PartialFunc1);

function Tclass._System.___hPartialFunc1_0(Ty) : Ty;

// Tclass._System.___hPartialFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc1(#$T0, #$R) } 
  Tclass._System.___hPartialFunc1_0(Tclass._System.___hPartialFunc1(#$T0, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc1_1(Ty) : Ty;

// Tclass._System.___hPartialFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc1(#$T0, #$R) } 
  Tclass._System.___hPartialFunc1_1(Tclass._System.___hPartialFunc1(#$T0, #$R))
     == #$R);

// Box/unbox axiom for Tclass._System.___hPartialFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hPartialFunc1(#$T0, #$R)) } 
  $IsBox(bx, Tclass._System.___hPartialFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc1(#$T0, #$R)));

// $Is axiom for subset type _System._#PartialFunc1
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc1(#$T0, #$R))
       && (forall x0#0: Box :: 
        $IsBox(x0#0, #$T0)
           ==> Set#Equal(Reads1(#$T0, #$R, $OneHeap, f#0, x0#0), Set#Empty(): Set)));

// $IsAlloc axiom for subset type _System._#PartialFunc1
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc1(#$T0, #$R), $h));

function Tclass._System.___hTotalFunc1(Ty, Ty) : Ty;

const unique Tagclass._System.___hTotalFunc1: TyTag;

// Tclass._System.___hTotalFunc1 Tag
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc1(#$T0, #$R) } 
  Tag(Tclass._System.___hTotalFunc1(#$T0, #$R)) == Tagclass._System.___hTotalFunc1
     && TagFamily(Tclass._System.___hTotalFunc1(#$T0, #$R)) == tytagFamily$_#TotalFunc1);

function Tclass._System.___hTotalFunc1_0(Ty) : Ty;

// Tclass._System.___hTotalFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc1(#$T0, #$R) } 
  Tclass._System.___hTotalFunc1_0(Tclass._System.___hTotalFunc1(#$T0, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc1_1(Ty) : Ty;

// Tclass._System.___hTotalFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc1(#$T0, #$R) } 
  Tclass._System.___hTotalFunc1_1(Tclass._System.___hTotalFunc1(#$T0, #$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hTotalFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hTotalFunc1(#$T0, #$R)) } 
  $IsBox(bx, Tclass._System.___hTotalFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc1(#$T0, #$R)));

// $Is axioms for subset type _System._#TotalFunc1
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R)) } 
  $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R))
     ==> $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R))
       && 
      (forall x0#0: Box :: 
        $IsBox(x0#0, #$T0) ==> Requires1#canCall(#$T0, #$R, $OneHeap, f#0, x0#0))
       && (forall x0#0: Box :: 
        $IsBox(x0#0, #$T0) ==> Requires1(#$T0, #$R, $OneHeap, f#0, x0#0)));

axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R))
       && ((forall x0#0: Box :: 
          $IsBox(x0#0, #$T0) ==> Requires1#canCall(#$T0, #$R, $OneHeap, f#0, x0#0))
         ==> (forall x0#0: Box :: 
          $IsBox(x0#0, #$T0) ==> Requires1(#$T0, #$R, $OneHeap, f#0, x0#0)))
     ==> $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R)));

// $IsAlloc axiom for subset type _System._#TotalFunc1
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R), $h));

function Tclass._System.___hFunc0(Ty) : Ty;

const unique Tagclass._System.___hFunc0: TyTag;

// Tclass._System.___hFunc0 Tag
axiom (forall #$R: Ty :: 
  { Tclass._System.___hFunc0(#$R) } 
  Tag(Tclass._System.___hFunc0(#$R)) == Tagclass._System.___hFunc0
     && TagFamily(Tclass._System.___hFunc0(#$R)) == tytagFamily$_#Func0);

function Tclass._System.___hFunc0_0(Ty) : Ty;

// Tclass._System.___hFunc0 injectivity 0
axiom (forall #$R: Ty :: 
  { Tclass._System.___hFunc0(#$R) } 
  Tclass._System.___hFunc0_0(Tclass._System.___hFunc0(#$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hFunc0
axiom (forall #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hFunc0(#$R)) } 
  $IsBox(bx, Tclass._System.___hFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc0(#$R)));

function Handle0([Heap]Box, [Heap]bool, [Heap]Set) : HandleType;

function Apply0(Ty, Heap, HandleType) : Box;

function Requires0(Ty, Heap, HandleType) : bool;

function Reads0(Ty, Heap, HandleType) : Set;

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set :: 
  { Apply0(t0, heap, Handle0(h, r, rd)) } 
  Apply0(t0, heap, Handle0(h, r, rd)) == h[heap]);

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set :: 
  { Requires0(t0, heap, Handle0(h, r, rd)) } 
  r[heap] ==> Requires0(t0, heap, Handle0(h, r, rd)));

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set, bx: Box :: 
  { Set#IsMember(Reads0(t0, heap, Handle0(h, r, rd)), bx) } 
  Set#IsMember(Reads0(t0, heap, Handle0(h, r, rd)), bx)
     == Set#IsMember(rd[heap], bx));

function {:inline} Requires0#canCall(t0: Ty, heap: Heap, f: HandleType) : bool
{
  true
}

function {:inline} Reads0#canCall(t0: Ty, heap: Heap, f: HandleType) : bool
{
  true
}

// frame axiom for Reads0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Reads0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads0(t0, h0, f), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads0(t0, h0, f) == Reads0(t0, h1, f));

// frame axiom for Reads0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Reads0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads0(t0, h1, f), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads0(t0, h0, f) == Reads0(t0, h1, f));

// frame axiom for Requires0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Requires0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads0(t0, h0, f), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires0(t0, h0, f) == Requires0(t0, h1, f));

// frame axiom for Requires0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Requires0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads0(t0, h1, f), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires0(t0, h0, f) == Requires0(t0, h1, f));

// frame axiom for Apply0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Apply0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads0(t0, h0, f), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply0(t0, h0, f) == Apply0(t0, h1, f));

// frame axiom for Apply0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Apply0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads0(t0, h1, f), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply0(t0, h0, f) == Apply0(t0, h1, f));

// empty-reads property for Reads0 
axiom (forall t0: Ty, heap: Heap, f: HandleType :: 
  { Reads0(t0, $OneHeap, f), $IsGoodHeap(heap) } { Reads0(t0, heap, f) } 
  $IsGoodHeap(heap) && $Is(f, Tclass._System.___hFunc0(t0))
     ==> (Set#Equal(Reads0(t0, $OneHeap, f), Set#Empty(): Set)
       <==> Set#Equal(Reads0(t0, heap, f), Set#Empty(): Set)));

// empty-reads property for Requires0
axiom (forall t0: Ty, heap: Heap, f: HandleType :: 
  { Requires0(t0, $OneHeap, f), $IsGoodHeap(heap) } { Requires0(t0, heap, f) } 
  $IsGoodHeap(heap)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && Set#Equal(Reads0(t0, $OneHeap, f), Set#Empty(): Set)
     ==> Requires0(t0, $OneHeap, f) == Requires0(t0, heap, f));

axiom (forall f: HandleType, t0: Ty :: 
  { $Is(f, Tclass._System.___hFunc0(t0)) } 
  $Is(f, Tclass._System.___hFunc0(t0))
     <==> (forall h: Heap :: 
      { Apply0(t0, h, f) } 
      $IsGoodHeap(h) && Requires0(t0, h, f) ==> $IsBox(Apply0(t0, h, f), t0)));

axiom (forall f: HandleType, t0: Ty, u0: Ty :: 
  { $Is(f, Tclass._System.___hFunc0(t0)), $Is(f, Tclass._System.___hFunc0(u0)) } 
  $Is(f, Tclass._System.___hFunc0(t0))
       && (forall bx: Box :: 
        { $IsBox(bx, t0) } { $IsBox(bx, u0) } 
        $IsBox(bx, t0) ==> $IsBox(bx, u0))
     ==> $Is(f, Tclass._System.___hFunc0(u0)));

axiom (forall f: HandleType, t0: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc0(t0), h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc0(t0), h)
       <==> Requires0(t0, h, f)
         ==> (forall r: ref :: 
          { Set#IsMember(Reads0(t0, h, f), $Box(r)) } 
          r != null && Set#IsMember(Reads0(t0, h, f), $Box(r))
             ==> $Unbox(read(h, r, alloc)): bool)));

axiom (forall f: HandleType, t0: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc0(t0), h) } 
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc0(t0), h)
     ==> 
    Requires0(t0, h, f)
     ==> $IsAllocBox(Apply0(t0, h, f), t0, h));

function Tclass._System.___hPartialFunc0(Ty) : Ty;

const unique Tagclass._System.___hPartialFunc0: TyTag;

// Tclass._System.___hPartialFunc0 Tag
axiom (forall #$R: Ty :: 
  { Tclass._System.___hPartialFunc0(#$R) } 
  Tag(Tclass._System.___hPartialFunc0(#$R)) == Tagclass._System.___hPartialFunc0
     && TagFamily(Tclass._System.___hPartialFunc0(#$R)) == tytagFamily$_#PartialFunc0);

function Tclass._System.___hPartialFunc0_0(Ty) : Ty;

// Tclass._System.___hPartialFunc0 injectivity 0
axiom (forall #$R: Ty :: 
  { Tclass._System.___hPartialFunc0(#$R) } 
  Tclass._System.___hPartialFunc0_0(Tclass._System.___hPartialFunc0(#$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hPartialFunc0
axiom (forall #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hPartialFunc0(#$R)) } 
  $IsBox(bx, Tclass._System.___hPartialFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc0(#$R)));

// $Is axiom for subset type _System._#PartialFunc0
axiom (forall #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hPartialFunc0(#$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc0(#$R))
     <==> $Is(f#0, Tclass._System.___hFunc0(#$R))
       && Set#Equal(Reads0(#$R, $OneHeap, f#0), Set#Empty(): Set));

// $IsAlloc axiom for subset type _System._#PartialFunc0
axiom (forall #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc0(#$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hPartialFunc0(#$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc0(#$R), $h));

function Tclass._System.___hTotalFunc0(Ty) : Ty;

const unique Tagclass._System.___hTotalFunc0: TyTag;

// Tclass._System.___hTotalFunc0 Tag
axiom (forall #$R: Ty :: 
  { Tclass._System.___hTotalFunc0(#$R) } 
  Tag(Tclass._System.___hTotalFunc0(#$R)) == Tagclass._System.___hTotalFunc0
     && TagFamily(Tclass._System.___hTotalFunc0(#$R)) == tytagFamily$_#TotalFunc0);

function Tclass._System.___hTotalFunc0_0(Ty) : Ty;

// Tclass._System.___hTotalFunc0 injectivity 0
axiom (forall #$R: Ty :: 
  { Tclass._System.___hTotalFunc0(#$R) } 
  Tclass._System.___hTotalFunc0_0(Tclass._System.___hTotalFunc0(#$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hTotalFunc0
axiom (forall #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hTotalFunc0(#$R)) } 
  $IsBox(bx, Tclass._System.___hTotalFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc0(#$R)));

// $Is axioms for subset type _System._#TotalFunc0
axiom (forall #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc0(#$R)) } 
  $Is(f#0, Tclass._System.___hTotalFunc0(#$R))
     ==> $Is(f#0, Tclass._System.___hPartialFunc0(#$R))
       && 
      Requires0#canCall(#$R, $OneHeap, f#0)
       && Requires0(#$R, $OneHeap, f#0));

axiom (forall #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc0(#$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc0(#$R))
       && (Requires0#canCall(#$R, $OneHeap, f#0) ==> Requires0(#$R, $OneHeap, f#0))
     ==> $Is(f#0, Tclass._System.___hTotalFunc0(#$R)));

// $IsAlloc axiom for subset type _System._#TotalFunc0
axiom (forall #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc0(#$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hTotalFunc0(#$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc0(#$R), $h));

const unique ##_System._tuple#2._#Make2: DtCtorId
uses {
// Constructor identifier
axiom (forall a#0#0#0: Box, a#0#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#0#0#0, a#0#1#0) } 
  DatatypeCtorId(#_System._tuple#2._#Make2(a#0#0#0, a#0#1#0))
     == ##_System._tuple#2._#Make2);
}

function _System.Tuple2.___hMake2_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _System.Tuple2.___hMake2_q(d) } 
  _System.Tuple2.___hMake2_q(d)
     <==> DatatypeCtorId(d) == ##_System._tuple#2._#Make2);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _System.Tuple2.___hMake2_q(d) } 
  _System.Tuple2.___hMake2_q(d)
     ==> (exists a#1#0#0: Box, a#1#1#0: Box :: 
      d == #_System._tuple#2._#Make2(a#1#0#0, a#1#1#0)));

const unique Tagclass._System.Tuple2: TyTag;

// Tclass._System.Tuple2 Tag
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty :: 
  { Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1) } 
  Tag(Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
       == Tagclass._System.Tuple2
     && TagFamily(Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
       == tytagFamily$_tuple#2);

function Tclass._System.Tuple2_0(Ty) : Ty;

// Tclass._System.Tuple2 injectivity 0
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty :: 
  { Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1) } 
  Tclass._System.Tuple2_0(Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     == _System._tuple#2$T0);

function Tclass._System.Tuple2_1(Ty) : Ty;

// Tclass._System.Tuple2 injectivity 1
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty :: 
  { Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1) } 
  Tclass._System.Tuple2_1(Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     == _System._tuple#2$T1);

// Box/unbox axiom for Tclass._System.Tuple2
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1)) } 
  $IsBox(bx, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, 
        Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1)));

// Constructor $Is
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty, a#2#0#0: Box, a#2#1#0: Box :: 
  { $Is(#_System._tuple#2._#Make2(a#2#0#0, a#2#1#0), 
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1)) } 
  $Is(#_System._tuple#2._#Make2(a#2#0#0, a#2#1#0), 
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     <==> $IsBox(a#2#0#0, _System._tuple#2$T0) && $IsBox(a#2#1#0, _System._tuple#2$T1));

// Constructor $IsAlloc
axiom (forall _System._tuple#2$T0: Ty, 
    _System._tuple#2$T1: Ty, 
    a#2#0#0: Box, 
    a#2#1#0: Box, 
    $h: Heap :: 
  { $IsAlloc(#_System._tuple#2._#Make2(a#2#0#0, a#2#1#0), 
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_System._tuple#2._#Make2(a#2#0#0, a#2#1#0), 
        Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), 
        $h)
       <==> $IsAllocBox(a#2#0#0, _System._tuple#2$T0, $h)
         && $IsAllocBox(a#2#1#0, _System._tuple#2$T1, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _System._tuple#2$T0: Ty, $h: Heap :: 
  { $IsAllocBox(_System.Tuple2._0(d), _System._tuple#2$T0, $h) } 
  $IsGoodHeap($h)
       && 
      _System.Tuple2.___hMake2_q(d)
       && (exists _System._tuple#2$T1: Ty :: 
        { $IsAlloc(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), $h) } 
        $IsAlloc(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), $h))
     ==> $IsAllocBox(_System.Tuple2._0(d), _System._tuple#2$T0, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _System._tuple#2$T1: Ty, $h: Heap :: 
  { $IsAllocBox(_System.Tuple2._1(d), _System._tuple#2$T1, $h) } 
  $IsGoodHeap($h)
       && 
      _System.Tuple2.___hMake2_q(d)
       && (exists _System._tuple#2$T0: Ty :: 
        { $IsAlloc(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), $h) } 
        $IsAlloc(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), $h))
     ==> $IsAllocBox(_System.Tuple2._1(d), _System._tuple#2$T1, $h));

// Constructor literal
axiom (forall a#3#0#0: Box, a#3#1#0: Box :: 
  { #_System._tuple#2._#Make2(Lit(a#3#0#0), Lit(a#3#1#0)) } 
  #_System._tuple#2._#Make2(Lit(a#3#0#0), Lit(a#3#1#0))
     == Lit(#_System._tuple#2._#Make2(a#3#0#0, a#3#1#0)));

// Constructor injectivity
axiom (forall a#4#0#0: Box, a#4#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#4#0#0, a#4#1#0) } 
  _System.Tuple2._0(#_System._tuple#2._#Make2(a#4#0#0, a#4#1#0)) == a#4#0#0);

// Inductive rank
axiom (forall a#5#0#0: Box, a#5#1#0: Box :: 
  { DtRank(#_System._tuple#2._#Make2(a#5#0#0, a#5#1#0)) } 
  BoxRank(a#5#0#0) < DtRank(#_System._tuple#2._#Make2(a#5#0#0, a#5#1#0)));

// Constructor injectivity
axiom (forall a#6#0#0: Box, a#6#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#6#0#0, a#6#1#0) } 
  _System.Tuple2._1(#_System._tuple#2._#Make2(a#6#0#0, a#6#1#0)) == a#6#1#0);

// Inductive rank
axiom (forall a#7#0#0: Box, a#7#1#0: Box :: 
  { DtRank(#_System._tuple#2._#Make2(a#7#0#0, a#7#1#0)) } 
  BoxRank(a#7#1#0) < DtRank(#_System._tuple#2._#Make2(a#7#0#0, a#7#1#0)));

// Depth-one case-split function
function $IsA#_System.Tuple2(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_System.Tuple2(d) } 
  $IsA#_System.Tuple2(d) ==> _System.Tuple2.___hMake2_q(d));

// Questionmark data type disjunctivity
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty, d: DatatypeType :: 
  { _System.Tuple2.___hMake2_q(d), $Is(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1)) } 
  $Is(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     ==> _System.Tuple2.___hMake2_q(d));

// Datatype extensional equality declaration
function _System.Tuple2#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_System._tuple#2._#Make2
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple2#Equal(a, b) } 
  _System.Tuple2#Equal(a, b)
     <==> _System.Tuple2._0(a) == _System.Tuple2._0(b)
       && _System.Tuple2._1(a) == _System.Tuple2._1(b));

// Datatype extensionality axiom: _System._tuple#2
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple2#Equal(a, b) } 
  _System.Tuple2#Equal(a, b) <==> a == b);

const unique class._System.Tuple2: ClassName;

// Constructor function declaration
function #_System._tuple#0._#Make0() : DatatypeType
uses {
// Constructor identifier
axiom DatatypeCtorId(#_System._tuple#0._#Make0()) == ##_System._tuple#0._#Make0;
// Constructor $Is
axiom $Is(#_System._tuple#0._#Make0(), Tclass._System.Tuple0());
// Constructor literal
axiom #_System._tuple#0._#Make0() == Lit(#_System._tuple#0._#Make0());
}

const unique ##_System._tuple#0._#Make0: DtCtorId
uses {
// Constructor identifier
axiom DatatypeCtorId(#_System._tuple#0._#Make0()) == ##_System._tuple#0._#Make0;
}

function _System.Tuple0.___hMake0_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _System.Tuple0.___hMake0_q(d) } 
  _System.Tuple0.___hMake0_q(d)
     <==> DatatypeCtorId(d) == ##_System._tuple#0._#Make0);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _System.Tuple0.___hMake0_q(d) } 
  _System.Tuple0.___hMake0_q(d) ==> d == #_System._tuple#0._#Make0());

function Tclass._System.Tuple0() : Ty
uses {
// Tclass._System.Tuple0 Tag
axiom Tag(Tclass._System.Tuple0()) == Tagclass._System.Tuple0
   && TagFamily(Tclass._System.Tuple0()) == tytagFamily$_tuple#0;
}

const unique Tagclass._System.Tuple0: TyTag;

// Box/unbox axiom for Tclass._System.Tuple0
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.Tuple0()) } 
  $IsBox(bx, Tclass._System.Tuple0())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._System.Tuple0()));

// Datatype $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(d, Tclass._System.Tuple0(), $h) } 
  $IsGoodHeap($h) && $Is(d, Tclass._System.Tuple0())
     ==> $IsAlloc(d, Tclass._System.Tuple0(), $h));

// Depth-one case-split function
function $IsA#_System.Tuple0(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_System.Tuple0(d) } 
  $IsA#_System.Tuple0(d) ==> _System.Tuple0.___hMake0_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _System.Tuple0.___hMake0_q(d), $Is(d, Tclass._System.Tuple0()) } 
  $Is(d, Tclass._System.Tuple0()) ==> _System.Tuple0.___hMake0_q(d));

// Datatype extensional equality declaration
function _System.Tuple0#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_System._tuple#0._#Make0
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple0#Equal(a, b) } 
  _System.Tuple0#Equal(a, b));

// Datatype extensionality axiom: _System._tuple#0
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple0#Equal(a, b) } 
  _System.Tuple0#Equal(a, b) <==> a == b);

const unique class._System.Tuple0: ClassName;

function Tclass._System.___hFunc2(Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hFunc2: TyTag;

// Tclass._System.___hFunc2 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc2(#$T0, #$T1, #$R) } 
  Tag(Tclass._System.___hFunc2(#$T0, #$T1, #$R)) == Tagclass._System.___hFunc2
     && TagFamily(Tclass._System.___hFunc2(#$T0, #$T1, #$R)) == tytagFamily$_#Func2);

function Tclass._System.___hFunc2_0(Ty) : Ty;

// Tclass._System.___hFunc2 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hFunc2_0(Tclass._System.___hFunc2(#$T0, #$T1, #$R)) == #$T0);

function Tclass._System.___hFunc2_1(Ty) : Ty;

// Tclass._System.___hFunc2 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hFunc2_1(Tclass._System.___hFunc2(#$T0, #$T1, #$R)) == #$T1);

function Tclass._System.___hFunc2_2(Ty) : Ty;

// Tclass._System.___hFunc2 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hFunc2_2(Tclass._System.___hFunc2(#$T0, #$T1, #$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hFunc2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hFunc2(#$T0, #$T1, #$R)) } 
  $IsBox(bx, Tclass._System.___hFunc2(#$T0, #$T1, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc2(#$T0, #$T1, #$R)));

function Handle2([Heap,Box,Box]Box, [Heap,Box,Box]bool, [Heap,Box,Box]Set) : HandleType;

function Apply2(Ty, Ty, Ty, Heap, HandleType, Box, Box) : Box;

function Requires2(Ty, Ty, Ty, Heap, HandleType, Box, Box) : bool;

function Reads2(Ty, Ty, Ty, Heap, HandleType, Box, Box) : Set;

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box]Box, 
    r: [Heap,Box,Box]bool, 
    rd: [Heap,Box,Box]Set, 
    bx0: Box, 
    bx1: Box :: 
  { Apply2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1) } 
  Apply2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1) == h[heap, bx0, bx1]);

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box]Box, 
    r: [Heap,Box,Box]bool, 
    rd: [Heap,Box,Box]Set, 
    bx0: Box, 
    bx1: Box :: 
  { Requires2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1) } 
  r[heap, bx0, bx1] ==> Requires2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1));

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box]Box, 
    r: [Heap,Box,Box]bool, 
    rd: [Heap,Box,Box]Set, 
    bx0: Box, 
    bx1: Box, 
    bx: Box :: 
  { Set#IsMember(Reads2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1), bx) } 
  Set#IsMember(Reads2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1), bx)
     == Set#IsMember(rd[heap, bx0, bx1], bx));

function {:inline} Requires2#canCall(t0: Ty, t1: Ty, t2: Ty, heap: Heap, f: HandleType, bx0: Box, bx1: Box) : bool
{
  true
}

function {:inline} Reads2#canCall(t0: Ty, t1: Ty, t2: Ty, heap: Heap, f: HandleType, bx0: Box, bx1: Box) : bool
{
  true
}

// frame axiom for Reads2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { $HeapSucc(h0, h1), Reads2(t0, t1, t2, h1, f, bx0, bx1) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads2(t0, t1, t2, h0, f, bx0, bx1), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads2(t0, t1, t2, h0, f, bx0, bx1) == Reads2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Reads2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { $HeapSucc(h0, h1), Reads2(t0, t1, t2, h1, f, bx0, bx1) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads2(t0, t1, t2, h1, f, bx0, bx1), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads2(t0, t1, t2, h0, f, bx0, bx1) == Reads2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Requires2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { $HeapSucc(h0, h1), Requires2(t0, t1, t2, h1, f, bx0, bx1) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads2(t0, t1, t2, h0, f, bx0, bx1), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires2(t0, t1, t2, h0, f, bx0, bx1) == Requires2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Requires2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { $HeapSucc(h0, h1), Requires2(t0, t1, t2, h1, f, bx0, bx1) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads2(t0, t1, t2, h1, f, bx0, bx1), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires2(t0, t1, t2, h0, f, bx0, bx1) == Requires2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Apply2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { $HeapSucc(h0, h1), Apply2(t0, t1, t2, h1, f, bx0, bx1) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads2(t0, t1, t2, h0, f, bx0, bx1), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply2(t0, t1, t2, h0, f, bx0, bx1) == Apply2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Apply2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { $HeapSucc(h0, h1), Apply2(t0, t1, t2, h1, f, bx0, bx1) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads2(t0, t1, t2, h1, f, bx0, bx1), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply2(t0, t1, t2, h0, f, bx0, bx1) == Apply2(t0, t1, t2, h1, f, bx0, bx1));

// empty-reads property for Reads2 
axiom (forall t0: Ty, t1: Ty, t2: Ty, heap: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { Reads2(t0, t1, t2, $OneHeap, f, bx0, bx1), $IsGoodHeap(heap) } 
    { Reads2(t0, t1, t2, heap, f, bx0, bx1) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
     ==> (Set#Equal(Reads2(t0, t1, t2, $OneHeap, f, bx0, bx1), Set#Empty(): Set)
       <==> Set#Equal(Reads2(t0, t1, t2, heap, f, bx0, bx1), Set#Empty(): Set)));

// empty-reads property for Requires2
axiom (forall t0: Ty, t1: Ty, t2: Ty, heap: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { Requires2(t0, t1, t2, $OneHeap, f, bx0, bx1), $IsGoodHeap(heap) } 
    { Requires2(t0, t1, t2, heap, f, bx0, bx1) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && Set#Equal(Reads2(t0, t1, t2, $OneHeap, f, bx0, bx1), Set#Empty(): Set)
     ==> Requires2(t0, t1, t2, $OneHeap, f, bx0, bx1)
       == Requires2(t0, t1, t2, heap, f, bx0, bx1));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty :: 
  { $Is(f, Tclass._System.___hFunc2(t0, t1, t2)) } 
  $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
     <==> (forall h: Heap, bx0: Box, bx1: Box :: 
      { Apply2(t0, t1, t2, h, f, bx0, bx1) } 
      $IsGoodHeap(h)
           && 
          $IsBox(bx0, t0)
           && $IsBox(bx1, t1)
           && Requires2(t0, t1, t2, h, f, bx0, bx1)
         ==> $IsBox(Apply2(t0, t1, t2, h, f, bx0, bx1), t2)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, u0: Ty, u1: Ty, u2: Ty :: 
  { $Is(f, Tclass._System.___hFunc2(t0, t1, t2)), $Is(f, Tclass._System.___hFunc2(u0, u1, u2)) } 
  $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall bx: Box :: 
        { $IsBox(bx, u0) } { $IsBox(bx, t0) } 
        $IsBox(bx, u0) ==> $IsBox(bx, t0))
       && (forall bx: Box :: 
        { $IsBox(bx, u1) } { $IsBox(bx, t1) } 
        $IsBox(bx, u1) ==> $IsBox(bx, t1))
       && (forall bx: Box :: 
        { $IsBox(bx, t2) } { $IsBox(bx, u2) } 
        $IsBox(bx, t2) ==> $IsBox(bx, u2))
     ==> $Is(f, Tclass._System.___hFunc2(u0, u1, u2)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc2(t0, t1, t2), h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc2(t0, t1, t2), h)
       <==> (forall bx0: Box, bx1: Box :: 
        { Apply2(t0, t1, t2, h, f, bx0, bx1) } { Reads2(t0, t1, t2, h, f, bx0, bx1) } 
        $IsBox(bx0, t0)
             && $IsAllocBox(bx0, t0, h)
             && 
            $IsBox(bx1, t1)
             && $IsAllocBox(bx1, t1, h)
             && Requires2(t0, t1, t2, h, f, bx0, bx1)
           ==> (forall r: ref :: 
            { Set#IsMember(Reads2(t0, t1, t2, h, f, bx0, bx1), $Box(r)) } 
            r != null && Set#IsMember(Reads2(t0, t1, t2, h, f, bx0, bx1), $Box(r))
               ==> $Unbox(read(h, r, alloc)): bool))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc2(t0, t1, t2), h) } 
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc2(t0, t1, t2), h)
     ==> (forall bx0: Box, bx1: Box :: 
      { Apply2(t0, t1, t2, h, f, bx0, bx1) } 
      $IsAllocBox(bx0, t0, h)
           && $IsAllocBox(bx1, t1, h)
           && Requires2(t0, t1, t2, h, f, bx0, bx1)
         ==> $IsAllocBox(Apply2(t0, t1, t2, h, f, bx0, bx1), t2, h)));

function Tclass._System.___hPartialFunc2(Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hPartialFunc2: TyTag;

// Tclass._System.___hPartialFunc2 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R) } 
  Tag(Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
       == Tagclass._System.___hPartialFunc2
     && TagFamily(Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
       == tytagFamily$_#PartialFunc2);

function Tclass._System.___hPartialFunc2_0(Ty) : Ty;

// Tclass._System.___hPartialFunc2 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hPartialFunc2_0(Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc2_1(Ty) : Ty;

// Tclass._System.___hPartialFunc2 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hPartialFunc2_1(Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     == #$T1);

function Tclass._System.___hPartialFunc2_2(Ty) : Ty;

// Tclass._System.___hPartialFunc2 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hPartialFunc2_2(Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     == #$R);

// Box/unbox axiom for Tclass._System.___hPartialFunc2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R)) } 
  $IsBox(bx, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R)));

// $Is axiom for subset type _System._#PartialFunc2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc2(#$T0, #$T1, #$R))
       && (forall x0#0: Box, x1#0: Box :: 
        $IsBox(x0#0, #$T0) && $IsBox(x1#0, #$T1)
           ==> Set#Equal(Reads2(#$T0, #$T1, #$R, $OneHeap, f#0, x0#0, x1#0), Set#Empty(): Set)));

// $IsAlloc axiom for subset type _System._#PartialFunc2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc2(#$T0, #$T1, #$R), $h));

function Tclass._System.___hTotalFunc2(Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hTotalFunc2: TyTag;

// Tclass._System.___hTotalFunc2 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R) } 
  Tag(Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
       == Tagclass._System.___hTotalFunc2
     && TagFamily(Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
       == tytagFamily$_#TotalFunc2);

function Tclass._System.___hTotalFunc2_0(Ty) : Ty;

// Tclass._System.___hTotalFunc2 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hTotalFunc2_0(Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc2_1(Ty) : Ty;

// Tclass._System.___hTotalFunc2 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hTotalFunc2_1(Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     == #$T1);

function Tclass._System.___hTotalFunc2_2(Ty) : Ty;

// Tclass._System.___hTotalFunc2 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hTotalFunc2_2(Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     == #$R);

// Box/unbox axiom for Tclass._System.___hTotalFunc2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R)) } 
  $IsBox(bx, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R)));

// $Is axioms for subset type _System._#TotalFunc2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R)) } 
  $Is(f#0, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     ==> $Is(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
       && 
      (forall x0#0: Box, x1#0: Box :: 
        $IsBox(x0#0, #$T0) && $IsBox(x1#0, #$T1)
           ==> Requires2#canCall(#$T0, #$T1, #$R, $OneHeap, f#0, x0#0, x1#0))
       && (forall x0#0: Box, x1#0: Box :: 
        $IsBox(x0#0, #$T0) && $IsBox(x1#0, #$T1)
           ==> Requires2(#$T0, #$T1, #$R, $OneHeap, f#0, x0#0, x1#0)));

axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
       && ((forall x0#0: Box, x1#0: Box :: 
          $IsBox(x0#0, #$T0) && $IsBox(x1#0, #$T1)
             ==> Requires2#canCall(#$T0, #$T1, #$R, $OneHeap, f#0, x0#0, x1#0))
         ==> (forall x0#0: Box, x1#0: Box :: 
          $IsBox(x0#0, #$T0) && $IsBox(x1#0, #$T1)
             ==> Requires2(#$T0, #$T1, #$R, $OneHeap, f#0, x0#0, x1#0)))
     ==> $Is(f#0, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R)));

// $IsAlloc axiom for subset type _System._#TotalFunc2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R), $h));

const unique class._module.__default: ClassName;

function Tclass._module.Node() : Ty
uses {
// Tclass._module.Node Tag
axiom Tag(Tclass._module.Node()) == Tagclass._module.Node
   && TagFamily(Tclass._module.Node()) == tytagFamily$Node;
}

const unique Tagclass._module.Node: TyTag;

// Box/unbox axiom for Tclass._module.Node
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Node()) } 
  $IsBox(bx, Tclass._module.Node())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Node()));

procedure {:verboseName "Bump (well-formedness)"} CheckWellFormed$$_module.__default.Bump(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap));
  modifies $Heap;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Bump (well-formedness)"} CheckWellFormed$$_module.__default.Bump(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref)
{
  var $_ModifiesFrame: [ref,Field]bool;


    // AddMethodImpl: Bump, CheckWellFormed$$_module.__default.Bump
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool
         ==> $o == a#0 || $o == b#0 || $o == c#0 || $o == d#0 || $o == e#0 || $o == f#0);
    assume {:captureState "Test/arith.dfy(14,7): initial state"} true;
    assume {:id "id0"} a#0 != b#0;
    assume {:id "id1"} a#0 != c#0;
    assume {:id "id2"} a#0 != d#0;
    assume {:id "id3"} a#0 != e#0;
    assume {:id "id4"} a#0 != f#0;
    assume {:id "id5"} b#0 != c#0;
    assume {:id "id6"} b#0 != d#0;
    assume {:id "id7"} b#0 != e#0;
    assume {:id "id8"} b#0 != f#0;
    assume {:id "id9"} c#0 != d#0;
    assume {:id "id10"} c#0 != e#0;
    assume {:id "id11"} c#0 != f#0;
    assume {:id "id12"} d#0 != e#0;
    assume {:id "id13"} d#0 != f#0;
    assume {:id "id14"} e#0 != f#0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
         ==> $Heap[$o] == old($Heap)[$o]
           || 
          $o == a#0
           || $o == b#0
           || $o == c#0
           || $o == d#0
           || $o == e#0
           || $o == f#0);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "Test/arith.dfy(20,84): post-state"} true;
    assert {:id "id15"} a#0 != null;
    assume true;
    assert {:id "id16"} a#0 != null;
    assert {:id "id17"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id18"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 1;
    assert {:id "id19"} a#0 != null;
    assume true;
    assert {:id "id20"} a#0 != null;
    assert {:id "id21"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id22"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id23"} a#0 != null;
    assume true;
    assert {:id "id24"} a#0 != null;
    assert {:id "id25"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id26"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id27"} a#0 != null;
    assume true;
    assert {:id "id28"} a#0 != null;
    assert {:id "id29"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id30"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
    assert {:id "id31"} b#0 != null;
    assume true;
    assert {:id "id32"} b#0 != null;
    assert {:id "id33"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id34"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 1;
    assert {:id "id35"} b#0 != null;
    assume true;
    assert {:id "id36"} b#0 != null;
    assert {:id "id37"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id38"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id39"} b#0 != null;
    assume true;
    assert {:id "id40"} b#0 != null;
    assert {:id "id41"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id42"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id43"} b#0 != null;
    assume true;
    assert {:id "id44"} b#0 != null;
    assert {:id "id45"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id46"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
    assert {:id "id47"} c#0 != null;
    assume true;
    assert {:id "id48"} c#0 != null;
    assert {:id "id49"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id50"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 1;
    assert {:id "id51"} c#0 != null;
    assume true;
    assert {:id "id52"} c#0 != null;
    assert {:id "id53"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id54"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id55"} c#0 != null;
    assume true;
    assert {:id "id56"} c#0 != null;
    assert {:id "id57"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id58"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id59"} c#0 != null;
    assume true;
    assert {:id "id60"} c#0 != null;
    assert {:id "id61"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id62"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
    assert {:id "id63"} d#0 != null;
    assume true;
    assert {:id "id64"} d#0 != null;
    assert {:id "id65"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id66"} $Unbox(read($Heap, d#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 1;
    assert {:id "id67"} d#0 != null;
    assume true;
    assert {:id "id68"} d#0 != null;
    assert {:id "id69"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id70"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
    assert {:id "id71"} d#0 != null;
    assume true;
    assert {:id "id72"} d#0 != null;
    assert {:id "id73"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id74"} $Unbox(read($Heap, d#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
    assert {:id "id75"} d#0 != null;
    assume true;
    assert {:id "id76"} d#0 != null;
    assert {:id "id77"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id78"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
    assert {:id "id79"} e#0 != null;
    assume true;
    assert {:id "id80"} e#0 != null;
    assert {:id "id81"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id82"} $Unbox(read($Heap, e#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 1;
    assert {:id "id83"} e#0 != null;
    assume true;
    assert {:id "id84"} e#0 != null;
    assert {:id "id85"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id86"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
    assert {:id "id87"} e#0 != null;
    assume true;
    assert {:id "id88"} e#0 != null;
    assert {:id "id89"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id90"} $Unbox(read($Heap, e#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
    assert {:id "id91"} e#0 != null;
    assume true;
    assert {:id "id92"} e#0 != null;
    assert {:id "id93"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id94"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
    assert {:id "id95"} f#0 != null;
    assume true;
    assert {:id "id96"} f#0 != null;
    assert {:id "id97"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id98"} $Unbox(read($Heap, f#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 1;
    assert {:id "id99"} f#0 != null;
    assume true;
    assert {:id "id100"} f#0 != null;
    assert {:id "id101"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id102"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
    assert {:id "id103"} f#0 != null;
    assume true;
    assert {:id "id104"} f#0 != null;
    assert {:id "id105"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id106"} $Unbox(read($Heap, f#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
    assert {:id "id107"} f#0 != null;
    assume true;
    assert {:id "id108"} f#0 != null;
    assert {:id "id109"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id110"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
}



procedure {:verboseName "Bump (call)"} Call$$_module.__default.Bump(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap));
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id111"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id112"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id113"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id114"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id115"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id116"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id117"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id118"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id119"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id120"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id121"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id122"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id123"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id124"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id125"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id126"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id127"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id128"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id129"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id130"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id131"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id132"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id133"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id134"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id135"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id136"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id137"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id138"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id139"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id140"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id141"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id142"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id143"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id144"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id145"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id146"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id147"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id148"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id149"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == a#0
         || $o == b#0
         || $o == c#0
         || $o == d#0
         || $o == e#0
         || $o == f#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "Bump (correctness)"} Impl$$_module.__default.Bump(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap))
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id150"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id151"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id152"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id153"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id154"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id155"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id156"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id157"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id158"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id159"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id160"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id161"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id162"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id163"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id164"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id165"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id166"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id167"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id168"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id169"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id170"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id171"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id172"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id173"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id174"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id175"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id176"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id177"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id178"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id179"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id180"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id181"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id182"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id183"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id184"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id185"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id186"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id187"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id188"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == a#0
         || $o == b#0
         || $o == c#0
         || $o == d#0
         || $o == e#0
         || $o == f#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Bump (correctness)"} Impl$$_module.__default.Bump(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref)
   returns ($_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var $rhs#0: int;
  var $rhs#1: int;
  var $rhs#2: int;
  var $rhs#3: int;
  var $rhs#4: int;
  var $rhs#5: int;

    // AddMethodImpl: Bump, Impl$$_module.__default.Bump
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool
         ==> $o == a#0 || $o == b#0 || $o == c#0 || $o == d#0 || $o == e#0 || $o == f#0);
    assume {:captureState "Test/arith.dfy(26,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(27,9)
    assert {:id "id189"} a#0 != null;
    assume true;
    assume true;
    assert {:id "id190"} $_ModifiesFrame[a#0, _module.Node.val];
    assert {:id "id191"} a#0 != null;
    assume true;
    assume true;
    $rhs#0 := $Unbox(read($Heap, a#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, a#0, _module.Node.val, $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    assume {:captureState "Test/arith.dfy(27,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(28,9)
    assert {:id "id194"} b#0 != null;
    assume true;
    assume true;
    assert {:id "id195"} $_ModifiesFrame[b#0, _module.Node.val];
    assert {:id "id196"} b#0 != null;
    assume true;
    assume true;
    $rhs#1 := $Unbox(read($Heap, b#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, b#0, _module.Node.val, $Box($rhs#1));
    assume $IsGoodHeap($Heap);
    assume {:captureState "Test/arith.dfy(28,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(29,9)
    assert {:id "id199"} c#0 != null;
    assume true;
    assume true;
    assert {:id "id200"} $_ModifiesFrame[c#0, _module.Node.val];
    assert {:id "id201"} c#0 != null;
    assume true;
    assume true;
    $rhs#2 := $Unbox(read($Heap, c#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, c#0, _module.Node.val, $Box($rhs#2));
    assume $IsGoodHeap($Heap);
    assume {:captureState "Test/arith.dfy(29,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(30,9)
    assert {:id "id204"} d#0 != null;
    assume true;
    assume true;
    assert {:id "id205"} $_ModifiesFrame[d#0, _module.Node.val];
    assert {:id "id206"} d#0 != null;
    assume true;
    assume true;
    $rhs#3 := $Unbox(read($Heap, d#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, d#0, _module.Node.val, $Box($rhs#3));
    assume $IsGoodHeap($Heap);
    assume {:captureState "Test/arith.dfy(30,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(31,9)
    assert {:id "id209"} e#0 != null;
    assume true;
    assume true;
    assert {:id "id210"} $_ModifiesFrame[e#0, _module.Node.val];
    assert {:id "id211"} e#0 != null;
    assume true;
    assume true;
    $rhs#4 := $Unbox(read($Heap, e#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, e#0, _module.Node.val, $Box($rhs#4));
    assume $IsGoodHeap($Heap);
    assume {:captureState "Test/arith.dfy(31,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(32,9)
    assert {:id "id214"} f#0 != null;
    assume true;
    assume true;
    assert {:id "id215"} $_ModifiesFrame[f#0, _module.Node.val];
    assert {:id "id216"} f#0 != null;
    assume true;
    assume true;
    $rhs#5 := $Unbox(read($Heap, f#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, f#0, _module.Node.val, $Box($rhs#5));
    assume $IsGoodHeap($Heap);
    assume {:captureState "Test/arith.dfy(32,20)"} true;
}



procedure {:verboseName "DoubleBump (well-formedness)"} CheckWellFormed$$_module.__default.DoubleBump(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap));
  modifies $Heap;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "DoubleBump (well-formedness)"} CheckWellFormed$$_module.__default.DoubleBump(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref)
{
  var $_ModifiesFrame: [ref,Field]bool;


    // AddMethodImpl: DoubleBump, CheckWellFormed$$_module.__default.DoubleBump
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool
         ==> $o == a#0 || $o == b#0 || $o == c#0 || $o == d#0 || $o == e#0 || $o == f#0);
    assume {:captureState "Test/arith.dfy(36,7): initial state"} true;
    assume {:id "id219"} a#0 != b#0;
    assume {:id "id220"} a#0 != c#0;
    assume {:id "id221"} a#0 != d#0;
    assume {:id "id222"} a#0 != e#0;
    assume {:id "id223"} a#0 != f#0;
    assume {:id "id224"} b#0 != c#0;
    assume {:id "id225"} b#0 != d#0;
    assume {:id "id226"} b#0 != e#0;
    assume {:id "id227"} b#0 != f#0;
    assume {:id "id228"} c#0 != d#0;
    assume {:id "id229"} c#0 != e#0;
    assume {:id "id230"} c#0 != f#0;
    assume {:id "id231"} d#0 != e#0;
    assume {:id "id232"} d#0 != f#0;
    assume {:id "id233"} e#0 != f#0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
         ==> $Heap[$o] == old($Heap)[$o]
           || 
          $o == a#0
           || $o == b#0
           || $o == c#0
           || $o == d#0
           || $o == e#0
           || $o == f#0);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "Test/arith.dfy(42,84): post-state"} true;
    assert {:id "id234"} a#0 != null;
    assume true;
    assert {:id "id235"} a#0 != null;
    assert {:id "id236"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id237"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 2;
    assert {:id "id238"} a#0 != null;
    assume true;
    assert {:id "id239"} a#0 != null;
    assert {:id "id240"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id241"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id242"} a#0 != null;
    assume true;
    assert {:id "id243"} a#0 != null;
    assert {:id "id244"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id245"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id246"} a#0 != null;
    assume true;
    assert {:id "id247"} a#0 != null;
    assert {:id "id248"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id249"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
    assert {:id "id250"} b#0 != null;
    assume true;
    assert {:id "id251"} b#0 != null;
    assert {:id "id252"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id253"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 2;
    assert {:id "id254"} b#0 != null;
    assume true;
    assert {:id "id255"} b#0 != null;
    assert {:id "id256"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id257"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id258"} b#0 != null;
    assume true;
    assert {:id "id259"} b#0 != null;
    assert {:id "id260"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id261"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id262"} b#0 != null;
    assume true;
    assert {:id "id263"} b#0 != null;
    assert {:id "id264"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id265"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
    assert {:id "id266"} c#0 != null;
    assume true;
    assert {:id "id267"} c#0 != null;
    assert {:id "id268"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id269"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 2;
    assert {:id "id270"} c#0 != null;
    assume true;
    assert {:id "id271"} c#0 != null;
    assert {:id "id272"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id273"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id274"} c#0 != null;
    assume true;
    assert {:id "id275"} c#0 != null;
    assert {:id "id276"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id277"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id278"} c#0 != null;
    assume true;
    assert {:id "id279"} c#0 != null;
    assert {:id "id280"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id281"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
    assert {:id "id282"} d#0 != null;
    assume true;
    assert {:id "id283"} d#0 != null;
    assert {:id "id284"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id285"} $Unbox(read($Heap, d#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 2;
    assert {:id "id286"} d#0 != null;
    assume true;
    assert {:id "id287"} d#0 != null;
    assert {:id "id288"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id289"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
    assert {:id "id290"} d#0 != null;
    assume true;
    assert {:id "id291"} d#0 != null;
    assert {:id "id292"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id293"} $Unbox(read($Heap, d#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
    assert {:id "id294"} d#0 != null;
    assume true;
    assert {:id "id295"} d#0 != null;
    assert {:id "id296"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id297"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
    assert {:id "id298"} e#0 != null;
    assume true;
    assert {:id "id299"} e#0 != null;
    assert {:id "id300"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id301"} $Unbox(read($Heap, e#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 2;
    assert {:id "id302"} e#0 != null;
    assume true;
    assert {:id "id303"} e#0 != null;
    assert {:id "id304"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id305"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
    assert {:id "id306"} e#0 != null;
    assume true;
    assert {:id "id307"} e#0 != null;
    assert {:id "id308"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id309"} $Unbox(read($Heap, e#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
    assert {:id "id310"} e#0 != null;
    assume true;
    assert {:id "id311"} e#0 != null;
    assert {:id "id312"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id313"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
    assert {:id "id314"} f#0 != null;
    assume true;
    assert {:id "id315"} f#0 != null;
    assert {:id "id316"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id317"} $Unbox(read($Heap, f#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 2;
    assert {:id "id318"} f#0 != null;
    assume true;
    assert {:id "id319"} f#0 != null;
    assert {:id "id320"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id321"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
    assert {:id "id322"} f#0 != null;
    assume true;
    assert {:id "id323"} f#0 != null;
    assert {:id "id324"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id325"} $Unbox(read($Heap, f#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
    assert {:id "id326"} f#0 != null;
    assume true;
    assert {:id "id327"} f#0 != null;
    assert {:id "id328"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id329"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
}



procedure {:verboseName "DoubleBump (call)"} Call$$_module.__default.DoubleBump(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap));
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id330"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id331"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id332"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id333"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id334"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id335"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id336"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id337"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id338"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id339"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id340"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id341"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id342"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id343"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id344"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id345"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id346"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id347"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id348"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id349"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id350"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id351"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id352"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id353"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id354"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id355"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id356"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id357"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id358"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id359"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id360"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id361"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id362"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id363"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id364"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id365"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id366"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id367"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id368"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == a#0
         || $o == b#0
         || $o == c#0
         || $o == d#0
         || $o == e#0
         || $o == f#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "DoubleBump (correctness)"} Impl$$_module.__default.DoubleBump(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap))
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id369"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id370"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id371"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id372"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id373"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id374"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id375"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id376"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id377"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id378"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id379"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id380"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id381"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id382"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id383"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id384"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id385"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id386"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id387"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id388"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id389"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id390"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id391"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id392"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id393"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id394"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id395"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id396"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id397"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id398"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id399"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id400"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id401"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id402"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id403"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id404"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id405"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id406"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id407"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == a#0
         || $o == b#0
         || $o == c#0
         || $o == d#0
         || $o == e#0
         || $o == f#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "DoubleBump (correctness)"} Impl$$_module.__default.DoubleBump(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref)
   returns ($_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var a##0: ref;
  var b##0: ref;
  var c##0: ref;
  var d##0: ref;
  var e##0: ref;
  var f##0: ref;
  var a##1: ref;
  var b##1: ref;
  var c##1: ref;
  var d##1: ref;
  var e##1: ref;
  var f##1: ref;

    // AddMethodImpl: DoubleBump, Impl$$_module.__default.DoubleBump
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool
         ==> $o == a#0 || $o == b#0 || $o == c#0 || $o == d#0 || $o == e#0 || $o == f#0);
    assume {:captureState "Test/arith.dfy(48,0): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(49,7)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := a#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##0 := b#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##0 := c#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##0 := d#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    e##0 := e#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    f##0 := f#0;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id408"} (forall $o: ref, $f: Field :: 
      $o != null
           && $Unbox(read($Heap, $o, alloc)): bool
           && (
            $o == a##0
             || $o == b##0
             || $o == c##0
             || $o == d##0
             || $o == e##0
             || $o == f##0)
         ==> $_ModifiesFrame[$o, $f]);
    call {:id "id409"} Call$$_module.__default.Bump(a##0, b##0, c##0, d##0, e##0, f##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(49,24)"} true;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(50,7)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##1 := a#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##1 := b#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##1 := c#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##1 := d#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    e##1 := e#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    f##1 := f#0;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id410"} (forall $o: ref, $f: Field :: 
      $o != null
           && $Unbox(read($Heap, $o, alloc)): bool
           && (
            $o == a##1
             || $o == b##1
             || $o == c##1
             || $o == d##1
             || $o == e##1
             || $o == f##1)
         ==> $_ModifiesFrame[$o, $f]);
    call {:id "id411"} Call$$_module.__default.Bump(a##1, b##1, c##1, d##1, e##1, f##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(50,24)"} true;
}



procedure {:verboseName "QuadBump (well-formedness)"} CheckWellFormed$$_module.__default.QuadBump(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap));
  modifies $Heap;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "QuadBump (well-formedness)"} CheckWellFormed$$_module.__default.QuadBump(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref)
{
  var $_ModifiesFrame: [ref,Field]bool;


    // AddMethodImpl: QuadBump, CheckWellFormed$$_module.__default.QuadBump
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool
         ==> $o == a#0 || $o == b#0 || $o == c#0 || $o == d#0 || $o == e#0 || $o == f#0);
    assume {:captureState "Test/arith.dfy(54,7): initial state"} true;
    assume {:id "id412"} a#0 != b#0;
    assume {:id "id413"} a#0 != c#0;
    assume {:id "id414"} a#0 != d#0;
    assume {:id "id415"} a#0 != e#0;
    assume {:id "id416"} a#0 != f#0;
    assume {:id "id417"} b#0 != c#0;
    assume {:id "id418"} b#0 != d#0;
    assume {:id "id419"} b#0 != e#0;
    assume {:id "id420"} b#0 != f#0;
    assume {:id "id421"} c#0 != d#0;
    assume {:id "id422"} c#0 != e#0;
    assume {:id "id423"} c#0 != f#0;
    assume {:id "id424"} d#0 != e#0;
    assume {:id "id425"} d#0 != f#0;
    assume {:id "id426"} e#0 != f#0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
         ==> $Heap[$o] == old($Heap)[$o]
           || 
          $o == a#0
           || $o == b#0
           || $o == c#0
           || $o == d#0
           || $o == e#0
           || $o == f#0);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "Test/arith.dfy(60,84): post-state"} true;
    assert {:id "id427"} a#0 != null;
    assume true;
    assert {:id "id428"} a#0 != null;
    assert {:id "id429"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id430"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 4;
    assert {:id "id431"} a#0 != null;
    assume true;
    assert {:id "id432"} a#0 != null;
    assert {:id "id433"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id434"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id435"} a#0 != null;
    assume true;
    assert {:id "id436"} a#0 != null;
    assert {:id "id437"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id438"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id439"} a#0 != null;
    assume true;
    assert {:id "id440"} a#0 != null;
    assert {:id "id441"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id442"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
    assert {:id "id443"} b#0 != null;
    assume true;
    assert {:id "id444"} b#0 != null;
    assert {:id "id445"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id446"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 4;
    assert {:id "id447"} b#0 != null;
    assume true;
    assert {:id "id448"} b#0 != null;
    assert {:id "id449"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id450"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id451"} b#0 != null;
    assume true;
    assert {:id "id452"} b#0 != null;
    assert {:id "id453"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id454"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id455"} b#0 != null;
    assume true;
    assert {:id "id456"} b#0 != null;
    assert {:id "id457"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id458"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
    assert {:id "id459"} c#0 != null;
    assume true;
    assert {:id "id460"} c#0 != null;
    assert {:id "id461"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id462"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 4;
    assert {:id "id463"} c#0 != null;
    assume true;
    assert {:id "id464"} c#0 != null;
    assert {:id "id465"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id466"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id467"} c#0 != null;
    assume true;
    assert {:id "id468"} c#0 != null;
    assert {:id "id469"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id470"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id471"} c#0 != null;
    assume true;
    assert {:id "id472"} c#0 != null;
    assert {:id "id473"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id474"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
    assert {:id "id475"} d#0 != null;
    assume true;
    assert {:id "id476"} d#0 != null;
    assert {:id "id477"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id478"} $Unbox(read($Heap, d#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 4;
    assert {:id "id479"} d#0 != null;
    assume true;
    assert {:id "id480"} d#0 != null;
    assert {:id "id481"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id482"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
    assert {:id "id483"} d#0 != null;
    assume true;
    assert {:id "id484"} d#0 != null;
    assert {:id "id485"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id486"} $Unbox(read($Heap, d#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
    assert {:id "id487"} d#0 != null;
    assume true;
    assert {:id "id488"} d#0 != null;
    assert {:id "id489"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id490"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
    assert {:id "id491"} e#0 != null;
    assume true;
    assert {:id "id492"} e#0 != null;
    assert {:id "id493"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id494"} $Unbox(read($Heap, e#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 4;
    assert {:id "id495"} e#0 != null;
    assume true;
    assert {:id "id496"} e#0 != null;
    assert {:id "id497"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id498"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
    assert {:id "id499"} e#0 != null;
    assume true;
    assert {:id "id500"} e#0 != null;
    assert {:id "id501"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id502"} $Unbox(read($Heap, e#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
    assert {:id "id503"} e#0 != null;
    assume true;
    assert {:id "id504"} e#0 != null;
    assert {:id "id505"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id506"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
    assert {:id "id507"} f#0 != null;
    assume true;
    assert {:id "id508"} f#0 != null;
    assert {:id "id509"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id510"} $Unbox(read($Heap, f#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 4;
    assert {:id "id511"} f#0 != null;
    assume true;
    assert {:id "id512"} f#0 != null;
    assert {:id "id513"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id514"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
    assert {:id "id515"} f#0 != null;
    assume true;
    assert {:id "id516"} f#0 != null;
    assert {:id "id517"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id518"} $Unbox(read($Heap, f#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
    assert {:id "id519"} f#0 != null;
    assume true;
    assert {:id "id520"} f#0 != null;
    assert {:id "id521"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id522"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
}



procedure {:verboseName "QuadBump (call)"} Call$$_module.__default.QuadBump(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap));
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id523"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id524"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id525"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id526"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id527"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id528"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id529"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id530"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id531"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id532"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id533"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id534"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id535"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id536"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id537"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id538"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id539"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id540"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id541"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id542"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id543"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id544"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id545"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id546"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id547"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id548"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id549"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id550"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id551"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id552"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id553"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id554"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id555"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id556"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id557"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id558"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id559"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id560"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id561"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == a#0
         || $o == b#0
         || $o == c#0
         || $o == d#0
         || $o == e#0
         || $o == f#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "QuadBump (correctness)"} Impl$$_module.__default.QuadBump(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap))
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id562"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id563"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id564"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id565"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id566"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id567"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id568"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id569"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id570"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id571"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id572"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id573"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id574"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id575"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id576"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id577"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id578"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id579"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id580"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id581"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id582"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id583"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id584"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id585"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id586"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id587"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id588"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id589"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id590"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id591"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id592"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id593"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id594"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id595"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id596"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id597"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id598"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id599"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id600"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == a#0
         || $o == b#0
         || $o == c#0
         || $o == d#0
         || $o == e#0
         || $o == f#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "QuadBump (correctness)"} Impl$$_module.__default.QuadBump(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref)
   returns ($_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var a##0: ref;
  var b##0: ref;
  var c##0: ref;
  var d##0: ref;
  var e##0: ref;
  var f##0: ref;
  var a##1: ref;
  var b##1: ref;
  var c##1: ref;
  var d##1: ref;
  var e##1: ref;
  var f##1: ref;

    // AddMethodImpl: QuadBump, Impl$$_module.__default.QuadBump
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool
         ==> $o == a#0 || $o == b#0 || $o == c#0 || $o == d#0 || $o == e#0 || $o == f#0);
    assume {:captureState "Test/arith.dfy(66,0): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(67,13)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := a#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##0 := b#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##0 := c#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##0 := d#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    e##0 := e#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    f##0 := f#0;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id601"} (forall $o: ref, $f: Field :: 
      $o != null
           && $Unbox(read($Heap, $o, alloc)): bool
           && (
            $o == a##0
             || $o == b##0
             || $o == c##0
             || $o == d##0
             || $o == e##0
             || $o == f##0)
         ==> $_ModifiesFrame[$o, $f]);
    call {:id "id602"} Call$$_module.__default.DoubleBump(a##0, b##0, c##0, d##0, e##0, f##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(67,30)"} true;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(68,13)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##1 := a#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##1 := b#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##1 := c#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##1 := d#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    e##1 := e#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    f##1 := f#0;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id603"} (forall $o: ref, $f: Field :: 
      $o != null
           && $Unbox(read($Heap, $o, alloc)): bool
           && (
            $o == a##1
             || $o == b##1
             || $o == c##1
             || $o == d##1
             || $o == e##1
             || $o == f##1)
         ==> $_ModifiesFrame[$o, $f]);
    call {:id "id604"} Call$$_module.__default.DoubleBump(a##1, b##1, c##1, d##1, e##1, f##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(68,30)"} true;
}



procedure {:verboseName "OctoBump (well-formedness)"} CheckWellFormed$$_module.__default.OctoBump(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap));
  modifies $Heap;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "OctoBump (well-formedness)"} CheckWellFormed$$_module.__default.OctoBump(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref)
{
  var $_ModifiesFrame: [ref,Field]bool;


    // AddMethodImpl: OctoBump, CheckWellFormed$$_module.__default.OctoBump
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool
         ==> $o == a#0 || $o == b#0 || $o == c#0 || $o == d#0 || $o == e#0 || $o == f#0);
    assume {:captureState "Test/arith.dfy(72,7): initial state"} true;
    assume {:id "id605"} a#0 != b#0;
    assume {:id "id606"} a#0 != c#0;
    assume {:id "id607"} a#0 != d#0;
    assume {:id "id608"} a#0 != e#0;
    assume {:id "id609"} a#0 != f#0;
    assume {:id "id610"} b#0 != c#0;
    assume {:id "id611"} b#0 != d#0;
    assume {:id "id612"} b#0 != e#0;
    assume {:id "id613"} b#0 != f#0;
    assume {:id "id614"} c#0 != d#0;
    assume {:id "id615"} c#0 != e#0;
    assume {:id "id616"} c#0 != f#0;
    assume {:id "id617"} d#0 != e#0;
    assume {:id "id618"} d#0 != f#0;
    assume {:id "id619"} e#0 != f#0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
         ==> $Heap[$o] == old($Heap)[$o]
           || 
          $o == a#0
           || $o == b#0
           || $o == c#0
           || $o == d#0
           || $o == e#0
           || $o == f#0);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "Test/arith.dfy(78,84): post-state"} true;
    assert {:id "id620"} a#0 != null;
    assume true;
    assert {:id "id621"} a#0 != null;
    assert {:id "id622"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id623"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 8;
    assert {:id "id624"} a#0 != null;
    assume true;
    assert {:id "id625"} a#0 != null;
    assert {:id "id626"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id627"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id628"} a#0 != null;
    assume true;
    assert {:id "id629"} a#0 != null;
    assert {:id "id630"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id631"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id632"} a#0 != null;
    assume true;
    assert {:id "id633"} a#0 != null;
    assert {:id "id634"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id635"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
    assert {:id "id636"} b#0 != null;
    assume true;
    assert {:id "id637"} b#0 != null;
    assert {:id "id638"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id639"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 8;
    assert {:id "id640"} b#0 != null;
    assume true;
    assert {:id "id641"} b#0 != null;
    assert {:id "id642"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id643"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id644"} b#0 != null;
    assume true;
    assert {:id "id645"} b#0 != null;
    assert {:id "id646"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id647"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id648"} b#0 != null;
    assume true;
    assert {:id "id649"} b#0 != null;
    assert {:id "id650"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id651"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
    assert {:id "id652"} c#0 != null;
    assume true;
    assert {:id "id653"} c#0 != null;
    assert {:id "id654"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id655"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 8;
    assert {:id "id656"} c#0 != null;
    assume true;
    assert {:id "id657"} c#0 != null;
    assert {:id "id658"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id659"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id660"} c#0 != null;
    assume true;
    assert {:id "id661"} c#0 != null;
    assert {:id "id662"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id663"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id664"} c#0 != null;
    assume true;
    assert {:id "id665"} c#0 != null;
    assert {:id "id666"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id667"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
    assert {:id "id668"} d#0 != null;
    assume true;
    assert {:id "id669"} d#0 != null;
    assert {:id "id670"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id671"} $Unbox(read($Heap, d#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 8;
    assert {:id "id672"} d#0 != null;
    assume true;
    assert {:id "id673"} d#0 != null;
    assert {:id "id674"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id675"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
    assert {:id "id676"} d#0 != null;
    assume true;
    assert {:id "id677"} d#0 != null;
    assert {:id "id678"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id679"} $Unbox(read($Heap, d#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
    assert {:id "id680"} d#0 != null;
    assume true;
    assert {:id "id681"} d#0 != null;
    assert {:id "id682"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id683"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
    assert {:id "id684"} e#0 != null;
    assume true;
    assert {:id "id685"} e#0 != null;
    assert {:id "id686"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id687"} $Unbox(read($Heap, e#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 8;
    assert {:id "id688"} e#0 != null;
    assume true;
    assert {:id "id689"} e#0 != null;
    assert {:id "id690"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id691"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
    assert {:id "id692"} e#0 != null;
    assume true;
    assert {:id "id693"} e#0 != null;
    assert {:id "id694"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id695"} $Unbox(read($Heap, e#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
    assert {:id "id696"} e#0 != null;
    assume true;
    assert {:id "id697"} e#0 != null;
    assert {:id "id698"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id699"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
    assert {:id "id700"} f#0 != null;
    assume true;
    assert {:id "id701"} f#0 != null;
    assert {:id "id702"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id703"} $Unbox(read($Heap, f#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 8;
    assert {:id "id704"} f#0 != null;
    assume true;
    assert {:id "id705"} f#0 != null;
    assert {:id "id706"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id707"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
    assert {:id "id708"} f#0 != null;
    assume true;
    assert {:id "id709"} f#0 != null;
    assert {:id "id710"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id711"} $Unbox(read($Heap, f#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
    assert {:id "id712"} f#0 != null;
    assume true;
    assert {:id "id713"} f#0 != null;
    assert {:id "id714"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id715"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
}



procedure {:verboseName "OctoBump (call)"} Call$$_module.__default.OctoBump(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap));
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id716"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id717"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id718"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id719"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id720"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id721"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id722"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id723"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id724"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id725"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id726"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id727"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id728"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id729"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id730"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id731"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id732"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id733"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id734"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id735"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id736"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id737"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id738"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id739"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id740"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id741"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id742"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id743"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id744"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id745"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id746"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id747"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id748"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id749"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id750"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id751"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id752"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id753"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id754"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == a#0
         || $o == b#0
         || $o == c#0
         || $o == d#0
         || $o == e#0
         || $o == f#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "OctoBump (correctness)"} Impl$$_module.__default.OctoBump(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap))
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id755"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id756"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id757"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id758"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id759"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id760"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id761"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id762"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id763"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id764"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id765"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id766"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id767"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id768"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id769"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id770"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id771"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id772"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id773"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id774"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id775"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id776"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id777"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id778"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id779"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id780"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id781"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id782"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id783"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id784"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id785"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id786"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id787"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id788"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id789"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id790"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id791"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id792"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id793"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == a#0
         || $o == b#0
         || $o == c#0
         || $o == d#0
         || $o == e#0
         || $o == f#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "OctoBump (correctness)"} Impl$$_module.__default.OctoBump(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref)
   returns ($_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var a##0: ref;
  var b##0: ref;
  var c##0: ref;
  var d##0: ref;
  var e##0: ref;
  var f##0: ref;
  var a##1: ref;
  var b##1: ref;
  var c##1: ref;
  var d##1: ref;
  var e##1: ref;
  var f##1: ref;

    // AddMethodImpl: OctoBump, Impl$$_module.__default.OctoBump
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool
         ==> $o == a#0 || $o == b#0 || $o == c#0 || $o == d#0 || $o == e#0 || $o == f#0);
    assume {:captureState "Test/arith.dfy(84,0): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(85,11)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := a#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##0 := b#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##0 := c#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##0 := d#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    e##0 := e#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    f##0 := f#0;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id794"} (forall $o: ref, $f: Field :: 
      $o != null
           && $Unbox(read($Heap, $o, alloc)): bool
           && (
            $o == a##0
             || $o == b##0
             || $o == c##0
             || $o == d##0
             || $o == e##0
             || $o == f##0)
         ==> $_ModifiesFrame[$o, $f]);
    call {:id "id795"} Call$$_module.__default.QuadBump(a##0, b##0, c##0, d##0, e##0, f##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(85,28)"} true;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(86,11)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##1 := a#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##1 := b#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##1 := c#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##1 := d#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    e##1 := e#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    f##1 := f#0;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id796"} (forall $o: ref, $f: Field :: 
      $o != null
           && $Unbox(read($Heap, $o, alloc)): bool
           && (
            $o == a##1
             || $o == b##1
             || $o == c##1
             || $o == d##1
             || $o == e##1
             || $o == f##1)
         ==> $_ModifiesFrame[$o, $f]);
    call {:id "id797"} Call$$_module.__default.QuadBump(a##1, b##1, c##1, d##1, e##1, f##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(86,28)"} true;
}



procedure {:verboseName "CrossBump (well-formedness)"} CheckWellFormed$$_module.__default.CrossBump(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Node()) && $IsAlloc(p#0, Tclass._module.Node(), $Heap), 
    q#0: ref
       where $Is(q#0, Tclass._module.Node()) && $IsAlloc(q#0, Tclass._module.Node(), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass._module.Node()) && $IsAlloc(r#0, Tclass._module.Node(), $Heap));
  modifies $Heap;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "CrossBump (well-formedness)"} CheckWellFormed$$_module.__default.CrossBump(a#0: ref, b#0: ref, c#0: ref, p#0: ref, q#0: ref, r#0: ref)
{
  var $_ModifiesFrame: [ref,Field]bool;


    // AddMethodImpl: CrossBump, CheckWellFormed$$_module.__default.CrossBump
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool
         ==> $o == a#0 || $o == b#0 || $o == c#0 || $o == p#0 || $o == q#0 || $o == r#0);
    assume {:captureState "Test/arith.dfy(93,7): initial state"} true;
    assume {:id "id798"} a#0 != b#0;
    assume {:id "id799"} a#0 != c#0;
    assume {:id "id800"} b#0 != c#0;
    assume {:id "id801"} p#0 != q#0;
    assume {:id "id802"} p#0 != r#0;
    assume {:id "id803"} q#0 != r#0;
    assume {:id "id804"} a#0 != p#0;
    assume {:id "id805"} a#0 != q#0;
    assume {:id "id806"} a#0 != r#0;
    assume {:id "id807"} b#0 != p#0;
    assume {:id "id808"} b#0 != q#0;
    assume {:id "id809"} b#0 != r#0;
    assume {:id "id810"} c#0 != p#0;
    assume {:id "id811"} c#0 != q#0;
    assume {:id "id812"} c#0 != r#0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
         ==> $Heap[$o] == old($Heap)[$o]
           || 
          $o == a#0
           || $o == b#0
           || $o == c#0
           || $o == p#0
           || $o == q#0
           || $o == r#0);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "Test/arith.dfy(100,84): post-state"} true;
    assert {:id "id813"} a#0 != null;
    assume true;
    assert {:id "id814"} a#0 != null;
    assert {:id "id815"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id816"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 1;
    assert {:id "id817"} a#0 != null;
    assume true;
    assert {:id "id818"} a#0 != null;
    assert {:id "id819"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id820"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id821"} a#0 != null;
    assume true;
    assert {:id "id822"} a#0 != null;
    assert {:id "id823"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id824"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id825"} a#0 != null;
    assume true;
    assert {:id "id826"} a#0 != null;
    assert {:id "id827"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id828"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
    assert {:id "id829"} b#0 != null;
    assume true;
    assert {:id "id830"} b#0 != null;
    assert {:id "id831"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id832"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 1;
    assert {:id "id833"} b#0 != null;
    assume true;
    assert {:id "id834"} b#0 != null;
    assert {:id "id835"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id836"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id837"} b#0 != null;
    assume true;
    assert {:id "id838"} b#0 != null;
    assert {:id "id839"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id840"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id841"} b#0 != null;
    assume true;
    assert {:id "id842"} b#0 != null;
    assert {:id "id843"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id844"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
    assert {:id "id845"} c#0 != null;
    assume true;
    assert {:id "id846"} c#0 != null;
    assert {:id "id847"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id848"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 1;
    assert {:id "id849"} c#0 != null;
    assume true;
    assert {:id "id850"} c#0 != null;
    assert {:id "id851"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id852"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id853"} c#0 != null;
    assume true;
    assert {:id "id854"} c#0 != null;
    assert {:id "id855"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id856"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id857"} c#0 != null;
    assume true;
    assert {:id "id858"} c#0 != null;
    assert {:id "id859"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id860"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
    assert {:id "id861"} p#0 != null;
    assume true;
    assert {:id "id862"} p#0 != null;
    assert {:id "id863"} $IsAlloc(p#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id864"} $Unbox(read($Heap, p#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), p#0, _module.Node.val)): int + 1;
    assert {:id "id865"} p#0 != null;
    assume true;
    assert {:id "id866"} p#0 != null;
    assert {:id "id867"} $IsAlloc(p#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id868"} $Unbox(read($Heap, p#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), p#0, _module.Node.tag)): int;
    assert {:id "id869"} p#0 != null;
    assume true;
    assert {:id "id870"} p#0 != null;
    assert {:id "id871"} $IsAlloc(p#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id872"} $Unbox(read($Heap, p#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), p#0, _module.Node.score)): int;
    assert {:id "id873"} p#0 != null;
    assume true;
    assert {:id "id874"} p#0 != null;
    assert {:id "id875"} $IsAlloc(p#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id876"} $Unbox(read($Heap, p#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), p#0, _module.Node.rank)): int;
    assert {:id "id877"} q#0 != null;
    assume true;
    assert {:id "id878"} q#0 != null;
    assert {:id "id879"} $IsAlloc(q#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id880"} $Unbox(read($Heap, q#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), q#0, _module.Node.val)): int + 1;
    assert {:id "id881"} q#0 != null;
    assume true;
    assert {:id "id882"} q#0 != null;
    assert {:id "id883"} $IsAlloc(q#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id884"} $Unbox(read($Heap, q#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), q#0, _module.Node.tag)): int;
    assert {:id "id885"} q#0 != null;
    assume true;
    assert {:id "id886"} q#0 != null;
    assert {:id "id887"} $IsAlloc(q#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id888"} $Unbox(read($Heap, q#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), q#0, _module.Node.score)): int;
    assert {:id "id889"} q#0 != null;
    assume true;
    assert {:id "id890"} q#0 != null;
    assert {:id "id891"} $IsAlloc(q#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id892"} $Unbox(read($Heap, q#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), q#0, _module.Node.rank)): int;
    assert {:id "id893"} r#0 != null;
    assume true;
    assert {:id "id894"} r#0 != null;
    assert {:id "id895"} $IsAlloc(r#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id896"} $Unbox(read($Heap, r#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), r#0, _module.Node.val)): int + 1;
    assert {:id "id897"} r#0 != null;
    assume true;
    assert {:id "id898"} r#0 != null;
    assert {:id "id899"} $IsAlloc(r#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id900"} $Unbox(read($Heap, r#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), r#0, _module.Node.tag)): int;
    assert {:id "id901"} r#0 != null;
    assume true;
    assert {:id "id902"} r#0 != null;
    assert {:id "id903"} $IsAlloc(r#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id904"} $Unbox(read($Heap, r#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), r#0, _module.Node.score)): int;
    assert {:id "id905"} r#0 != null;
    assume true;
    assert {:id "id906"} r#0 != null;
    assert {:id "id907"} $IsAlloc(r#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id908"} $Unbox(read($Heap, r#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), r#0, _module.Node.rank)): int;
}



procedure {:verboseName "CrossBump (call)"} Call$$_module.__default.CrossBump(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Node()) && $IsAlloc(p#0, Tclass._module.Node(), $Heap), 
    q#0: ref
       where $Is(q#0, Tclass._module.Node()) && $IsAlloc(q#0, Tclass._module.Node(), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass._module.Node()) && $IsAlloc(r#0, Tclass._module.Node(), $Heap));
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id909"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id910"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id911"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id912"} p#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id913"} p#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id914"} q#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id915"} a#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id916"} a#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id917"} a#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id918"} b#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id919"} b#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id920"} b#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id921"} c#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id922"} c#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id923"} c#0 != r#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id924"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id925"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id926"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id927"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id928"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id929"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id930"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id931"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id932"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id933"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id934"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id935"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id936"} $Unbox(read($Heap, p#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id937"} $Unbox(read($Heap, p#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id938"} $Unbox(read($Heap, p#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id939"} $Unbox(read($Heap, p#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id940"} $Unbox(read($Heap, q#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id941"} $Unbox(read($Heap, q#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id942"} $Unbox(read($Heap, q#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id943"} $Unbox(read($Heap, q#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id944"} $Unbox(read($Heap, r#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id945"} $Unbox(read($Heap, r#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id946"} $Unbox(read($Heap, r#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id947"} $Unbox(read($Heap, r#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.rank)): int;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == a#0
         || $o == b#0
         || $o == c#0
         || $o == p#0
         || $o == q#0
         || $o == r#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "CrossBump (correctness)"} Impl$$_module.__default.CrossBump(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Node()) && $IsAlloc(p#0, Tclass._module.Node(), $Heap), 
    q#0: ref
       where $Is(q#0, Tclass._module.Node()) && $IsAlloc(q#0, Tclass._module.Node(), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass._module.Node()) && $IsAlloc(r#0, Tclass._module.Node(), $Heap))
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id948"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id949"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id950"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id951"} p#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id952"} p#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id953"} q#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id954"} a#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id955"} a#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id956"} a#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id957"} b#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id958"} b#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id959"} b#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id960"} c#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id961"} c#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id962"} c#0 != r#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id963"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id964"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id965"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id966"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id967"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id968"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id969"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id970"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id971"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id972"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id973"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id974"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id975"} $Unbox(read($Heap, p#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id976"} $Unbox(read($Heap, p#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id977"} $Unbox(read($Heap, p#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id978"} $Unbox(read($Heap, p#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id979"} $Unbox(read($Heap, q#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id980"} $Unbox(read($Heap, q#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id981"} $Unbox(read($Heap, q#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id982"} $Unbox(read($Heap, q#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id983"} $Unbox(read($Heap, r#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id984"} $Unbox(read($Heap, r#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id985"} $Unbox(read($Heap, r#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id986"} $Unbox(read($Heap, r#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.rank)): int;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == a#0
         || $o == b#0
         || $o == c#0
         || $o == p#0
         || $o == q#0
         || $o == r#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "CrossBump (correctness)"} Impl$$_module.__default.CrossBump(a#0: ref, b#0: ref, c#0: ref, p#0: ref, q#0: ref, r#0: ref)
   returns ($_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var $rhs#0: int;
  var $rhs#1: int;
  var $rhs#2: int;
  var $rhs#3: int;
  var $rhs#4: int;
  var $rhs#5: int;

    // AddMethodImpl: CrossBump, Impl$$_module.__default.CrossBump
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool
         ==> $o == a#0 || $o == b#0 || $o == c#0 || $o == p#0 || $o == q#0 || $o == r#0);
    assume {:captureState "Test/arith.dfy(106,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(107,9)
    assert {:id "id987"} a#0 != null;
    assume true;
    assume true;
    assert {:id "id988"} $_ModifiesFrame[a#0, _module.Node.val];
    assert {:id "id989"} a#0 != null;
    assume true;
    assume true;
    $rhs#0 := $Unbox(read($Heap, a#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, a#0, _module.Node.val, $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    assume {:captureState "Test/arith.dfy(107,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(108,9)
    assert {:id "id992"} b#0 != null;
    assume true;
    assume true;
    assert {:id "id993"} $_ModifiesFrame[b#0, _module.Node.val];
    assert {:id "id994"} b#0 != null;
    assume true;
    assume true;
    $rhs#1 := $Unbox(read($Heap, b#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, b#0, _module.Node.val, $Box($rhs#1));
    assume $IsGoodHeap($Heap);
    assume {:captureState "Test/arith.dfy(108,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(109,9)
    assert {:id "id997"} c#0 != null;
    assume true;
    assume true;
    assert {:id "id998"} $_ModifiesFrame[c#0, _module.Node.val];
    assert {:id "id999"} c#0 != null;
    assume true;
    assume true;
    $rhs#2 := $Unbox(read($Heap, c#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, c#0, _module.Node.val, $Box($rhs#2));
    assume $IsGoodHeap($Heap);
    assume {:captureState "Test/arith.dfy(109,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(110,9)
    assert {:id "id1002"} p#0 != null;
    assume true;
    assume true;
    assert {:id "id1003"} $_ModifiesFrame[p#0, _module.Node.val];
    assert {:id "id1004"} p#0 != null;
    assume true;
    assume true;
    $rhs#3 := $Unbox(read($Heap, p#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, p#0, _module.Node.val, $Box($rhs#3));
    assume $IsGoodHeap($Heap);
    assume {:captureState "Test/arith.dfy(110,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(111,9)
    assert {:id "id1007"} q#0 != null;
    assume true;
    assume true;
    assert {:id "id1008"} $_ModifiesFrame[q#0, _module.Node.val];
    assert {:id "id1009"} q#0 != null;
    assume true;
    assume true;
    $rhs#4 := $Unbox(read($Heap, q#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, q#0, _module.Node.val, $Box($rhs#4));
    assume $IsGoodHeap($Heap);
    assume {:captureState "Test/arith.dfy(111,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(112,9)
    assert {:id "id1012"} r#0 != null;
    assume true;
    assume true;
    assert {:id "id1013"} $_ModifiesFrame[r#0, _module.Node.val];
    assert {:id "id1014"} r#0 != null;
    assume true;
    assume true;
    $rhs#5 := $Unbox(read($Heap, r#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, r#0, _module.Node.val, $Box($rhs#5));
    assume $IsGoodHeap($Heap);
    assume {:captureState "Test/arith.dfy(112,20)"} true;
}



procedure {:verboseName "BumpN (well-formedness)"} CheckWellFormed$$_module.__default.BumpN(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap), 
    n#0: int);
  modifies $Heap;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "BumpN (well-formedness)"} CheckWellFormed$$_module.__default.BumpN(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref, n#0: int)
{
  var $_ModifiesFrame: [ref,Field]bool;


    // AddMethodImpl: BumpN, CheckWellFormed$$_module.__default.BumpN
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool
         ==> $o == a#0 || $o == b#0 || $o == c#0 || $o == d#0 || $o == e#0 || $o == f#0);
    assume {:captureState "Test/arith.dfy(119,7): initial state"} true;
    assume {:id "id1017"} n#0 >= LitInt(0);
    assume {:id "id1018"} a#0 != b#0;
    assume {:id "id1019"} a#0 != c#0;
    assume {:id "id1020"} a#0 != d#0;
    assume {:id "id1021"} a#0 != e#0;
    assume {:id "id1022"} a#0 != f#0;
    assume {:id "id1023"} b#0 != c#0;
    assume {:id "id1024"} b#0 != d#0;
    assume {:id "id1025"} b#0 != e#0;
    assume {:id "id1026"} b#0 != f#0;
    assume {:id "id1027"} c#0 != d#0;
    assume {:id "id1028"} c#0 != e#0;
    assume {:id "id1029"} c#0 != f#0;
    assume {:id "id1030"} d#0 != e#0;
    assume {:id "id1031"} d#0 != f#0;
    assume {:id "id1032"} e#0 != f#0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
         ==> $Heap[$o] == old($Heap)[$o]
           || 
          $o == a#0
           || $o == b#0
           || $o == c#0
           || $o == d#0
           || $o == e#0
           || $o == f#0);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "Test/arith.dfy(126,86): post-state"} true;
    assert {:id "id1033"} a#0 != null;
    assume true;
    assert {:id "id1034"} a#0 != null;
    assert {:id "id1035"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1036"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
    assert {:id "id1037"} a#0 != null;
    assume true;
    assert {:id "id1038"} a#0 != null;
    assert {:id "id1039"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1040"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id1041"} a#0 != null;
    assume true;
    assert {:id "id1042"} a#0 != null;
    assert {:id "id1043"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1044"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id1045"} a#0 != null;
    assume true;
    assert {:id "id1046"} a#0 != null;
    assert {:id "id1047"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1048"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
    assert {:id "id1049"} b#0 != null;
    assume true;
    assert {:id "id1050"} b#0 != null;
    assert {:id "id1051"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1052"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
    assert {:id "id1053"} b#0 != null;
    assume true;
    assert {:id "id1054"} b#0 != null;
    assert {:id "id1055"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1056"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id1057"} b#0 != null;
    assume true;
    assert {:id "id1058"} b#0 != null;
    assert {:id "id1059"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1060"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id1061"} b#0 != null;
    assume true;
    assert {:id "id1062"} b#0 != null;
    assert {:id "id1063"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1064"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
    assert {:id "id1065"} c#0 != null;
    assume true;
    assert {:id "id1066"} c#0 != null;
    assert {:id "id1067"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1068"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
    assert {:id "id1069"} c#0 != null;
    assume true;
    assert {:id "id1070"} c#0 != null;
    assert {:id "id1071"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1072"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id1073"} c#0 != null;
    assume true;
    assert {:id "id1074"} c#0 != null;
    assert {:id "id1075"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1076"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id1077"} c#0 != null;
    assume true;
    assert {:id "id1078"} c#0 != null;
    assert {:id "id1079"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1080"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
    assert {:id "id1081"} d#0 != null;
    assume true;
    assert {:id "id1082"} d#0 != null;
    assert {:id "id1083"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1084"} $Unbox(read($Heap, d#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
    assert {:id "id1085"} d#0 != null;
    assume true;
    assert {:id "id1086"} d#0 != null;
    assert {:id "id1087"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1088"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
    assert {:id "id1089"} d#0 != null;
    assume true;
    assert {:id "id1090"} d#0 != null;
    assert {:id "id1091"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1092"} $Unbox(read($Heap, d#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
    assert {:id "id1093"} d#0 != null;
    assume true;
    assert {:id "id1094"} d#0 != null;
    assert {:id "id1095"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1096"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
    assert {:id "id1097"} e#0 != null;
    assume true;
    assert {:id "id1098"} e#0 != null;
    assert {:id "id1099"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1100"} $Unbox(read($Heap, e#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
    assert {:id "id1101"} e#0 != null;
    assume true;
    assert {:id "id1102"} e#0 != null;
    assert {:id "id1103"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1104"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
    assert {:id "id1105"} e#0 != null;
    assume true;
    assert {:id "id1106"} e#0 != null;
    assert {:id "id1107"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1108"} $Unbox(read($Heap, e#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
    assert {:id "id1109"} e#0 != null;
    assume true;
    assert {:id "id1110"} e#0 != null;
    assert {:id "id1111"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1112"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
    assert {:id "id1113"} f#0 != null;
    assume true;
    assert {:id "id1114"} f#0 != null;
    assert {:id "id1115"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1116"} $Unbox(read($Heap, f#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
    assert {:id "id1117"} f#0 != null;
    assume true;
    assert {:id "id1118"} f#0 != null;
    assert {:id "id1119"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1120"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
    assert {:id "id1121"} f#0 != null;
    assume true;
    assert {:id "id1122"} f#0 != null;
    assert {:id "id1123"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1124"} $Unbox(read($Heap, f#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
    assert {:id "id1125"} f#0 != null;
    assume true;
    assert {:id "id1126"} f#0 != null;
    assert {:id "id1127"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1128"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
}



procedure {:verboseName "BumpN (call)"} Call$$_module.__default.BumpN(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap), 
    n#0: int);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id1129"} n#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id1130"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id1131"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1132"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1133"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1134"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1135"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1136"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1137"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1138"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1139"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1140"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1141"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1142"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1143"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1144"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id1145"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1146"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1147"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1148"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1149"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1150"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1151"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1152"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1153"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1154"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1155"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1156"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1157"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1158"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1159"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1160"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1161"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1162"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1163"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1164"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1165"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1166"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1167"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1168"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == a#0
         || $o == b#0
         || $o == c#0
         || $o == d#0
         || $o == e#0
         || $o == f#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "BumpN (correctness)"} Impl$$_module.__default.BumpN(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap), 
    n#0: int)
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id1169"} n#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id1170"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id1171"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1172"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1173"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1174"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1175"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1176"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1177"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1178"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1179"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1180"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1181"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1182"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1183"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1184"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id1185"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1186"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1187"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1188"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1189"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1190"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1191"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1192"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1193"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1194"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1195"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1196"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1197"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1198"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1199"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1200"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1201"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1202"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1203"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1204"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1205"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1206"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1207"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1208"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == a#0
         || $o == b#0
         || $o == c#0
         || $o == d#0
         || $o == e#0
         || $o == f#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "BumpN (correctness)"} Impl$$_module.__default.BumpN(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref, n#0: int)
   returns ($_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var a##0_0: ref;
  var b##0_0: ref;
  var c##0_0: ref;
  var d##0_0: ref;
  var e##0_0: ref;
  var f##0_0: ref;

    // AddMethodImpl: BumpN, Impl$$_module.__default.BumpN
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool
         ==> $o == a#0 || $o == b#0 || $o == c#0 || $o == d#0 || $o == e#0 || $o == f#0);
    assume {:captureState "Test/arith.dfy(132,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(133,9)
    assume true;
    assume true;
    i#0 := LitInt(0);
    assume {:captureState "Test/arith.dfy(133,12)"} true;
    // ----- while statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(134,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := n#0 - i#0;
    havoc $w$loop#0;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume $w$loop#0 ==> true;
    while (true)
      free invariant true;
      invariant {:id "id1211"} $w$loop#0 ==> LitInt(0) <= i#0;
      invariant {:id "id1212"} $w$loop#0 ==> i#0 <= n#0;
      free invariant true;
      invariant {:id "id1226"} $w$loop#0
         ==> $Unbox(read($Heap, a#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(2), i#0);
      invariant {:id "id1227"} $w$loop#0
         ==> $Unbox(read($Heap, a#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
      invariant {:id "id1228"} $w$loop#0
         ==> $Unbox(read($Heap, a#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
      invariant {:id "id1229"} $w$loop#0
         ==> $Unbox(read($Heap, a#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1243"} $w$loop#0
         ==> $Unbox(read($Heap, b#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(2), i#0);
      invariant {:id "id1244"} $w$loop#0
         ==> $Unbox(read($Heap, b#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
      invariant {:id "id1245"} $w$loop#0
         ==> $Unbox(read($Heap, b#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
      invariant {:id "id1246"} $w$loop#0
         ==> $Unbox(read($Heap, b#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1260"} $w$loop#0
         ==> $Unbox(read($Heap, c#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(2), i#0);
      invariant {:id "id1261"} $w$loop#0
         ==> $Unbox(read($Heap, c#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
      invariant {:id "id1262"} $w$loop#0
         ==> $Unbox(read($Heap, c#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
      invariant {:id "id1263"} $w$loop#0
         ==> $Unbox(read($Heap, c#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1277"} $w$loop#0
         ==> $Unbox(read($Heap, d#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(2), i#0);
      invariant {:id "id1278"} $w$loop#0
         ==> $Unbox(read($Heap, d#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
      invariant {:id "id1279"} $w$loop#0
         ==> $Unbox(read($Heap, d#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
      invariant {:id "id1280"} $w$loop#0
         ==> $Unbox(read($Heap, d#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1294"} $w$loop#0
         ==> $Unbox(read($Heap, e#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(2), i#0);
      invariant {:id "id1295"} $w$loop#0
         ==> $Unbox(read($Heap, e#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
      invariant {:id "id1296"} $w$loop#0
         ==> $Unbox(read($Heap, e#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
      invariant {:id "id1297"} $w$loop#0
         ==> $Unbox(read($Heap, e#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1311"} $w$loop#0
         ==> $Unbox(read($Heap, f#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(2), i#0);
      invariant {:id "id1312"} $w$loop#0
         ==> $Unbox(read($Heap, f#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
      invariant {:id "id1313"} $w$loop#0
         ==> $Unbox(read($Heap, f#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
      invariant {:id "id1314"} $w$loop#0
         ==> $Unbox(read($Heap, f#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]
             || 
            $o == a#0
             || $o == b#0
             || $o == c#0
             || $o == d#0
             || $o == e#0
             || $o == f#0);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall $o: ref, $f: Field :: 
        { read($Heap, $o, $f) } 
        $o != null && $Unbox(read($PreLoopHeap$loop#0, $o, alloc)): bool
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f)
             || $_ModifiesFrame[$o, $f]);
      free invariant n#0 - i#0 <= $decr_init$loop#00;
    {
        assume {:captureState "Test/arith.dfy(134,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (LitInt(0) <= i#0)
            {
            }

            assume true;
            assume {:id "id1210"} LitInt(0) <= i#0 && i#0 <= n#0;
            assert {:id "id1213"} {:subsumption 0} a#0 != null;
            assume true;
            assert {:id "id1214"} {:subsumption 0} a#0 != null;
            assert {:id "id1215"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
            assume true;
            if ($Unbox(read($Heap, a#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(2), i#0))
            {
                assert {:id "id1216"} {:subsumption 0} a#0 != null;
                assume true;
                assert {:id "id1217"} {:subsumption 0} a#0 != null;
                assert {:id "id1218"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, a#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, a#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int)
            {
                assert {:id "id1219"} {:subsumption 0} a#0 != null;
                assume true;
                assert {:id "id1220"} {:subsumption 0} a#0 != null;
                assert {:id "id1221"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, a#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, a#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int
               && $Unbox(read($Heap, a#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.score)): int)
            {
                assert {:id "id1222"} {:subsumption 0} a#0 != null;
                assume true;
                assert {:id "id1223"} {:subsumption 0} a#0 != null;
                assert {:id "id1224"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            assume true;
            assume {:id "id1225"} $Unbox(read($Heap, a#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, a#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int
               && $Unbox(read($Heap, a#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.score)): int
               && $Unbox(read($Heap, a#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
            assert {:id "id1230"} {:subsumption 0} b#0 != null;
            assume true;
            assert {:id "id1231"} {:subsumption 0} b#0 != null;
            assert {:id "id1232"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
            assume true;
            if ($Unbox(read($Heap, b#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(2), i#0))
            {
                assert {:id "id1233"} {:subsumption 0} b#0 != null;
                assume true;
                assert {:id "id1234"} {:subsumption 0} b#0 != null;
                assert {:id "id1235"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, b#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, b#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int)
            {
                assert {:id "id1236"} {:subsumption 0} b#0 != null;
                assume true;
                assert {:id "id1237"} {:subsumption 0} b#0 != null;
                assert {:id "id1238"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, b#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, b#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int
               && $Unbox(read($Heap, b#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.score)): int)
            {
                assert {:id "id1239"} {:subsumption 0} b#0 != null;
                assume true;
                assert {:id "id1240"} {:subsumption 0} b#0 != null;
                assert {:id "id1241"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            assume true;
            assume {:id "id1242"} $Unbox(read($Heap, b#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, b#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int
               && $Unbox(read($Heap, b#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.score)): int
               && $Unbox(read($Heap, b#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
            assert {:id "id1247"} {:subsumption 0} c#0 != null;
            assume true;
            assert {:id "id1248"} {:subsumption 0} c#0 != null;
            assert {:id "id1249"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
            assume true;
            if ($Unbox(read($Heap, c#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(2), i#0))
            {
                assert {:id "id1250"} {:subsumption 0} c#0 != null;
                assume true;
                assert {:id "id1251"} {:subsumption 0} c#0 != null;
                assert {:id "id1252"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, c#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, c#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int)
            {
                assert {:id "id1253"} {:subsumption 0} c#0 != null;
                assume true;
                assert {:id "id1254"} {:subsumption 0} c#0 != null;
                assert {:id "id1255"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, c#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, c#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int
               && $Unbox(read($Heap, c#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.score)): int)
            {
                assert {:id "id1256"} {:subsumption 0} c#0 != null;
                assume true;
                assert {:id "id1257"} {:subsumption 0} c#0 != null;
                assert {:id "id1258"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            assume true;
            assume {:id "id1259"} $Unbox(read($Heap, c#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, c#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int
               && $Unbox(read($Heap, c#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.score)): int
               && $Unbox(read($Heap, c#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
            assert {:id "id1264"} {:subsumption 0} d#0 != null;
            assume true;
            assert {:id "id1265"} {:subsumption 0} d#0 != null;
            assert {:id "id1266"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
            assume true;
            if ($Unbox(read($Heap, d#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(2), i#0))
            {
                assert {:id "id1267"} {:subsumption 0} d#0 != null;
                assume true;
                assert {:id "id1268"} {:subsumption 0} d#0 != null;
                assert {:id "id1269"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, d#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, d#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int)
            {
                assert {:id "id1270"} {:subsumption 0} d#0 != null;
                assume true;
                assert {:id "id1271"} {:subsumption 0} d#0 != null;
                assert {:id "id1272"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, d#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, d#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int
               && $Unbox(read($Heap, d#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.score)): int)
            {
                assert {:id "id1273"} {:subsumption 0} d#0 != null;
                assume true;
                assert {:id "id1274"} {:subsumption 0} d#0 != null;
                assert {:id "id1275"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            assume true;
            assume {:id "id1276"} $Unbox(read($Heap, d#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, d#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int
               && $Unbox(read($Heap, d#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.score)): int
               && $Unbox(read($Heap, d#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
            assert {:id "id1281"} {:subsumption 0} e#0 != null;
            assume true;
            assert {:id "id1282"} {:subsumption 0} e#0 != null;
            assert {:id "id1283"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
            assume true;
            if ($Unbox(read($Heap, e#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(2), i#0))
            {
                assert {:id "id1284"} {:subsumption 0} e#0 != null;
                assume true;
                assert {:id "id1285"} {:subsumption 0} e#0 != null;
                assert {:id "id1286"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, e#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, e#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int)
            {
                assert {:id "id1287"} {:subsumption 0} e#0 != null;
                assume true;
                assert {:id "id1288"} {:subsumption 0} e#0 != null;
                assert {:id "id1289"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, e#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, e#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int
               && $Unbox(read($Heap, e#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.score)): int)
            {
                assert {:id "id1290"} {:subsumption 0} e#0 != null;
                assume true;
                assert {:id "id1291"} {:subsumption 0} e#0 != null;
                assert {:id "id1292"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            assume true;
            assume {:id "id1293"} $Unbox(read($Heap, e#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, e#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int
               && $Unbox(read($Heap, e#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.score)): int
               && $Unbox(read($Heap, e#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
            assert {:id "id1298"} {:subsumption 0} f#0 != null;
            assume true;
            assert {:id "id1299"} {:subsumption 0} f#0 != null;
            assert {:id "id1300"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
            assume true;
            if ($Unbox(read($Heap, f#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(2), i#0))
            {
                assert {:id "id1301"} {:subsumption 0} f#0 != null;
                assume true;
                assert {:id "id1302"} {:subsumption 0} f#0 != null;
                assert {:id "id1303"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, f#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, f#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int)
            {
                assert {:id "id1304"} {:subsumption 0} f#0 != null;
                assume true;
                assert {:id "id1305"} {:subsumption 0} f#0 != null;
                assert {:id "id1306"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, f#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, f#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int
               && $Unbox(read($Heap, f#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.score)): int)
            {
                assert {:id "id1307"} {:subsumption 0} f#0 != null;
                assume true;
                assert {:id "id1308"} {:subsumption 0} f#0 != null;
                assert {:id "id1309"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            assume true;
            assume {:id "id1310"} $Unbox(read($Heap, f#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, f#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int
               && $Unbox(read($Heap, f#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.score)): int
               && $Unbox(read($Heap, f#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
            assume true;
            assume false;
        }

        assume true;
        if (n#0 <= i#0)
        {
            break;
        }

        assume true;
        $decr$loop#00 := n#0 - i#0;
        // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(143,15)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##0_0 := a#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        b##0_0 := b#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##0_0 := c#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        d##0_0 := d#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        e##0_0 := e#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        f##0_0 := f#0;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assert {:id "id1315"} (forall $o: ref, $f: Field :: 
          $o != null
               && $Unbox(read($Heap, $o, alloc)): bool
               && (
                $o == a##0_0
                 || $o == b##0_0
                 || $o == c##0_0
                 || $o == d##0_0
                 || $o == e##0_0
                 || $o == f##0_0)
             ==> $_ModifiesFrame[$o, $f]);
        call {:id "id1316"} Call$$_module.__default.DoubleBump(a##0_0, b##0_0, c##0_0, d##0_0, e##0_0, f##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "Test/arith.dfy(143,32)"} true;
        // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(144,7)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "Test/arith.dfy(144,14)"} true;
        assume true;
        // ----- loop termination check ----- /Users/saline/development/projects/dafny/Test/arith.dfy(134,3)
        assert {:id "id1318"} 0 <= $decr$loop#00 || n#0 - i#0 == $decr$loop#00;
        assert {:id "id1319"} n#0 - i#0 < $decr$loop#00;
        assume true;
    }
}



procedure {:verboseName "BumpNQuad (well-formedness)"} CheckWellFormed$$_module.__default.BumpNQuad(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap), 
    n#0: int);
  modifies $Heap;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "BumpNQuad (well-formedness)"} CheckWellFormed$$_module.__default.BumpNQuad(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref, n#0: int)
{
  var $_ModifiesFrame: [ref,Field]bool;


    // AddMethodImpl: BumpNQuad, CheckWellFormed$$_module.__default.BumpNQuad
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool
         ==> $o == a#0 || $o == b#0 || $o == c#0 || $o == d#0 || $o == e#0 || $o == f#0);
    assume {:captureState "Test/arith.dfy(152,7): initial state"} true;
    assume {:id "id1320"} n#0 >= LitInt(0);
    assume {:id "id1321"} a#0 != b#0;
    assume {:id "id1322"} a#0 != c#0;
    assume {:id "id1323"} a#0 != d#0;
    assume {:id "id1324"} a#0 != e#0;
    assume {:id "id1325"} a#0 != f#0;
    assume {:id "id1326"} b#0 != c#0;
    assume {:id "id1327"} b#0 != d#0;
    assume {:id "id1328"} b#0 != e#0;
    assume {:id "id1329"} b#0 != f#0;
    assume {:id "id1330"} c#0 != d#0;
    assume {:id "id1331"} c#0 != e#0;
    assume {:id "id1332"} c#0 != f#0;
    assume {:id "id1333"} d#0 != e#0;
    assume {:id "id1334"} d#0 != f#0;
    assume {:id "id1335"} e#0 != f#0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
         ==> $Heap[$o] == old($Heap)[$o]
           || 
          $o == a#0
           || $o == b#0
           || $o == c#0
           || $o == d#0
           || $o == e#0
           || $o == f#0);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "Test/arith.dfy(159,86): post-state"} true;
    assert {:id "id1336"} a#0 != null;
    assume true;
    assert {:id "id1337"} a#0 != null;
    assert {:id "id1338"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1339"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
    assert {:id "id1340"} a#0 != null;
    assume true;
    assert {:id "id1341"} a#0 != null;
    assert {:id "id1342"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1343"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id1344"} a#0 != null;
    assume true;
    assert {:id "id1345"} a#0 != null;
    assert {:id "id1346"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1347"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id1348"} a#0 != null;
    assume true;
    assert {:id "id1349"} a#0 != null;
    assert {:id "id1350"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1351"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
    assert {:id "id1352"} b#0 != null;
    assume true;
    assert {:id "id1353"} b#0 != null;
    assert {:id "id1354"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1355"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
    assert {:id "id1356"} b#0 != null;
    assume true;
    assert {:id "id1357"} b#0 != null;
    assert {:id "id1358"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1359"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id1360"} b#0 != null;
    assume true;
    assert {:id "id1361"} b#0 != null;
    assert {:id "id1362"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1363"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id1364"} b#0 != null;
    assume true;
    assert {:id "id1365"} b#0 != null;
    assert {:id "id1366"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1367"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
    assert {:id "id1368"} c#0 != null;
    assume true;
    assert {:id "id1369"} c#0 != null;
    assert {:id "id1370"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1371"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
    assert {:id "id1372"} c#0 != null;
    assume true;
    assert {:id "id1373"} c#0 != null;
    assert {:id "id1374"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1375"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id1376"} c#0 != null;
    assume true;
    assert {:id "id1377"} c#0 != null;
    assert {:id "id1378"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1379"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id1380"} c#0 != null;
    assume true;
    assert {:id "id1381"} c#0 != null;
    assert {:id "id1382"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1383"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
    assert {:id "id1384"} d#0 != null;
    assume true;
    assert {:id "id1385"} d#0 != null;
    assert {:id "id1386"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1387"} $Unbox(read($Heap, d#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
    assert {:id "id1388"} d#0 != null;
    assume true;
    assert {:id "id1389"} d#0 != null;
    assert {:id "id1390"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1391"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
    assert {:id "id1392"} d#0 != null;
    assume true;
    assert {:id "id1393"} d#0 != null;
    assert {:id "id1394"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1395"} $Unbox(read($Heap, d#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
    assert {:id "id1396"} d#0 != null;
    assume true;
    assert {:id "id1397"} d#0 != null;
    assert {:id "id1398"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1399"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
    assert {:id "id1400"} e#0 != null;
    assume true;
    assert {:id "id1401"} e#0 != null;
    assert {:id "id1402"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1403"} $Unbox(read($Heap, e#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
    assert {:id "id1404"} e#0 != null;
    assume true;
    assert {:id "id1405"} e#0 != null;
    assert {:id "id1406"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1407"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
    assert {:id "id1408"} e#0 != null;
    assume true;
    assert {:id "id1409"} e#0 != null;
    assert {:id "id1410"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1411"} $Unbox(read($Heap, e#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
    assert {:id "id1412"} e#0 != null;
    assume true;
    assert {:id "id1413"} e#0 != null;
    assert {:id "id1414"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1415"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
    assert {:id "id1416"} f#0 != null;
    assume true;
    assert {:id "id1417"} f#0 != null;
    assert {:id "id1418"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1419"} $Unbox(read($Heap, f#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
    assert {:id "id1420"} f#0 != null;
    assume true;
    assert {:id "id1421"} f#0 != null;
    assert {:id "id1422"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1423"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
    assert {:id "id1424"} f#0 != null;
    assume true;
    assert {:id "id1425"} f#0 != null;
    assert {:id "id1426"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1427"} $Unbox(read($Heap, f#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
    assert {:id "id1428"} f#0 != null;
    assume true;
    assert {:id "id1429"} f#0 != null;
    assert {:id "id1430"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1431"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
}



procedure {:verboseName "BumpNQuad (call)"} Call$$_module.__default.BumpNQuad(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap), 
    n#0: int);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id1432"} n#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id1433"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id1434"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1435"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1436"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1437"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1438"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1439"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1440"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1441"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1442"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1443"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1444"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1445"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1446"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1447"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id1448"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1449"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1450"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1451"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1452"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1453"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1454"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1455"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1456"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1457"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1458"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1459"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1460"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1461"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1462"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1463"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1464"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1465"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1466"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1467"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1468"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1469"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1470"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1471"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == a#0
         || $o == b#0
         || $o == c#0
         || $o == d#0
         || $o == e#0
         || $o == f#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "BumpNQuad (correctness)"} Impl$$_module.__default.BumpNQuad(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap), 
    n#0: int)
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id1472"} n#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id1473"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id1474"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1475"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1476"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1477"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1478"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1479"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1480"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1481"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1482"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1483"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1484"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1485"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1486"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1487"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id1488"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1489"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1490"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1491"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1492"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1493"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1494"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1495"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1496"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1497"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1498"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1499"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1500"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1501"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1502"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1503"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1504"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1505"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1506"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1507"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1508"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1509"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1510"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1511"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == a#0
         || $o == b#0
         || $o == c#0
         || $o == d#0
         || $o == e#0
         || $o == f#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "BumpNQuad (correctness)"} Impl$$_module.__default.BumpNQuad(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref, n#0: int)
   returns ($_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var a##0_0: ref;
  var b##0_0: ref;
  var c##0_0: ref;
  var d##0_0: ref;
  var e##0_0: ref;
  var f##0_0: ref;

    // AddMethodImpl: BumpNQuad, Impl$$_module.__default.BumpNQuad
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool
         ==> $o == a#0 || $o == b#0 || $o == c#0 || $o == d#0 || $o == e#0 || $o == f#0);
    assume {:captureState "Test/arith.dfy(165,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(166,9)
    assume true;
    assume true;
    i#0 := LitInt(0);
    assume {:captureState "Test/arith.dfy(166,12)"} true;
    // ----- while statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(167,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := n#0 - i#0;
    havoc $w$loop#0;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume $w$loop#0 ==> true;
    while (true)
      free invariant true;
      invariant {:id "id1514"} $w$loop#0 ==> LitInt(0) <= i#0;
      invariant {:id "id1515"} $w$loop#0 ==> i#0 <= n#0;
      free invariant true;
      invariant {:id "id1529"} $w$loop#0
         ==> $Unbox(read($Heap, a#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(4), i#0);
      invariant {:id "id1530"} $w$loop#0
         ==> $Unbox(read($Heap, a#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
      invariant {:id "id1531"} $w$loop#0
         ==> $Unbox(read($Heap, a#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
      invariant {:id "id1532"} $w$loop#0
         ==> $Unbox(read($Heap, a#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1546"} $w$loop#0
         ==> $Unbox(read($Heap, b#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(4), i#0);
      invariant {:id "id1547"} $w$loop#0
         ==> $Unbox(read($Heap, b#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
      invariant {:id "id1548"} $w$loop#0
         ==> $Unbox(read($Heap, b#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
      invariant {:id "id1549"} $w$loop#0
         ==> $Unbox(read($Heap, b#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1563"} $w$loop#0
         ==> $Unbox(read($Heap, c#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(4), i#0);
      invariant {:id "id1564"} $w$loop#0
         ==> $Unbox(read($Heap, c#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
      invariant {:id "id1565"} $w$loop#0
         ==> $Unbox(read($Heap, c#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
      invariant {:id "id1566"} $w$loop#0
         ==> $Unbox(read($Heap, c#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1580"} $w$loop#0
         ==> $Unbox(read($Heap, d#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(4), i#0);
      invariant {:id "id1581"} $w$loop#0
         ==> $Unbox(read($Heap, d#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
      invariant {:id "id1582"} $w$loop#0
         ==> $Unbox(read($Heap, d#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
      invariant {:id "id1583"} $w$loop#0
         ==> $Unbox(read($Heap, d#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1597"} $w$loop#0
         ==> $Unbox(read($Heap, e#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(4), i#0);
      invariant {:id "id1598"} $w$loop#0
         ==> $Unbox(read($Heap, e#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
      invariant {:id "id1599"} $w$loop#0
         ==> $Unbox(read($Heap, e#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
      invariant {:id "id1600"} $w$loop#0
         ==> $Unbox(read($Heap, e#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1614"} $w$loop#0
         ==> $Unbox(read($Heap, f#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(4), i#0);
      invariant {:id "id1615"} $w$loop#0
         ==> $Unbox(read($Heap, f#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
      invariant {:id "id1616"} $w$loop#0
         ==> $Unbox(read($Heap, f#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
      invariant {:id "id1617"} $w$loop#0
         ==> $Unbox(read($Heap, f#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]
             || 
            $o == a#0
             || $o == b#0
             || $o == c#0
             || $o == d#0
             || $o == e#0
             || $o == f#0);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall $o: ref, $f: Field :: 
        { read($Heap, $o, $f) } 
        $o != null && $Unbox(read($PreLoopHeap$loop#0, $o, alloc)): bool
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f)
             || $_ModifiesFrame[$o, $f]);
      free invariant n#0 - i#0 <= $decr_init$loop#00;
    {
        assume {:captureState "Test/arith.dfy(167,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (LitInt(0) <= i#0)
            {
            }

            assume true;
            assume {:id "id1513"} LitInt(0) <= i#0 && i#0 <= n#0;
            assert {:id "id1516"} {:subsumption 0} a#0 != null;
            assume true;
            assert {:id "id1517"} {:subsumption 0} a#0 != null;
            assert {:id "id1518"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
            assume true;
            if ($Unbox(read($Heap, a#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(4), i#0))
            {
                assert {:id "id1519"} {:subsumption 0} a#0 != null;
                assume true;
                assert {:id "id1520"} {:subsumption 0} a#0 != null;
                assert {:id "id1521"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, a#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, a#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int)
            {
                assert {:id "id1522"} {:subsumption 0} a#0 != null;
                assume true;
                assert {:id "id1523"} {:subsumption 0} a#0 != null;
                assert {:id "id1524"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, a#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, a#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int
               && $Unbox(read($Heap, a#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.score)): int)
            {
                assert {:id "id1525"} {:subsumption 0} a#0 != null;
                assume true;
                assert {:id "id1526"} {:subsumption 0} a#0 != null;
                assert {:id "id1527"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            assume true;
            assume {:id "id1528"} $Unbox(read($Heap, a#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, a#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int
               && $Unbox(read($Heap, a#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.score)): int
               && $Unbox(read($Heap, a#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
            assert {:id "id1533"} {:subsumption 0} b#0 != null;
            assume true;
            assert {:id "id1534"} {:subsumption 0} b#0 != null;
            assert {:id "id1535"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
            assume true;
            if ($Unbox(read($Heap, b#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(4), i#0))
            {
                assert {:id "id1536"} {:subsumption 0} b#0 != null;
                assume true;
                assert {:id "id1537"} {:subsumption 0} b#0 != null;
                assert {:id "id1538"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, b#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, b#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int)
            {
                assert {:id "id1539"} {:subsumption 0} b#0 != null;
                assume true;
                assert {:id "id1540"} {:subsumption 0} b#0 != null;
                assert {:id "id1541"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, b#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, b#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int
               && $Unbox(read($Heap, b#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.score)): int)
            {
                assert {:id "id1542"} {:subsumption 0} b#0 != null;
                assume true;
                assert {:id "id1543"} {:subsumption 0} b#0 != null;
                assert {:id "id1544"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            assume true;
            assume {:id "id1545"} $Unbox(read($Heap, b#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, b#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int
               && $Unbox(read($Heap, b#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.score)): int
               && $Unbox(read($Heap, b#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
            assert {:id "id1550"} {:subsumption 0} c#0 != null;
            assume true;
            assert {:id "id1551"} {:subsumption 0} c#0 != null;
            assert {:id "id1552"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
            assume true;
            if ($Unbox(read($Heap, c#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(4), i#0))
            {
                assert {:id "id1553"} {:subsumption 0} c#0 != null;
                assume true;
                assert {:id "id1554"} {:subsumption 0} c#0 != null;
                assert {:id "id1555"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, c#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, c#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int)
            {
                assert {:id "id1556"} {:subsumption 0} c#0 != null;
                assume true;
                assert {:id "id1557"} {:subsumption 0} c#0 != null;
                assert {:id "id1558"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, c#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, c#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int
               && $Unbox(read($Heap, c#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.score)): int)
            {
                assert {:id "id1559"} {:subsumption 0} c#0 != null;
                assume true;
                assert {:id "id1560"} {:subsumption 0} c#0 != null;
                assert {:id "id1561"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            assume true;
            assume {:id "id1562"} $Unbox(read($Heap, c#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, c#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int
               && $Unbox(read($Heap, c#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.score)): int
               && $Unbox(read($Heap, c#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
            assert {:id "id1567"} {:subsumption 0} d#0 != null;
            assume true;
            assert {:id "id1568"} {:subsumption 0} d#0 != null;
            assert {:id "id1569"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
            assume true;
            if ($Unbox(read($Heap, d#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(4), i#0))
            {
                assert {:id "id1570"} {:subsumption 0} d#0 != null;
                assume true;
                assert {:id "id1571"} {:subsumption 0} d#0 != null;
                assert {:id "id1572"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, d#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, d#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int)
            {
                assert {:id "id1573"} {:subsumption 0} d#0 != null;
                assume true;
                assert {:id "id1574"} {:subsumption 0} d#0 != null;
                assert {:id "id1575"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, d#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, d#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int
               && $Unbox(read($Heap, d#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.score)): int)
            {
                assert {:id "id1576"} {:subsumption 0} d#0 != null;
                assume true;
                assert {:id "id1577"} {:subsumption 0} d#0 != null;
                assert {:id "id1578"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            assume true;
            assume {:id "id1579"} $Unbox(read($Heap, d#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, d#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int
               && $Unbox(read($Heap, d#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.score)): int
               && $Unbox(read($Heap, d#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
            assert {:id "id1584"} {:subsumption 0} e#0 != null;
            assume true;
            assert {:id "id1585"} {:subsumption 0} e#0 != null;
            assert {:id "id1586"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
            assume true;
            if ($Unbox(read($Heap, e#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(4), i#0))
            {
                assert {:id "id1587"} {:subsumption 0} e#0 != null;
                assume true;
                assert {:id "id1588"} {:subsumption 0} e#0 != null;
                assert {:id "id1589"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, e#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, e#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int)
            {
                assert {:id "id1590"} {:subsumption 0} e#0 != null;
                assume true;
                assert {:id "id1591"} {:subsumption 0} e#0 != null;
                assert {:id "id1592"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, e#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, e#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int
               && $Unbox(read($Heap, e#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.score)): int)
            {
                assert {:id "id1593"} {:subsumption 0} e#0 != null;
                assume true;
                assert {:id "id1594"} {:subsumption 0} e#0 != null;
                assert {:id "id1595"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            assume true;
            assume {:id "id1596"} $Unbox(read($Heap, e#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, e#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int
               && $Unbox(read($Heap, e#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.score)): int
               && $Unbox(read($Heap, e#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
            assert {:id "id1601"} {:subsumption 0} f#0 != null;
            assume true;
            assert {:id "id1602"} {:subsumption 0} f#0 != null;
            assert {:id "id1603"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
            assume true;
            if ($Unbox(read($Heap, f#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(4), i#0))
            {
                assert {:id "id1604"} {:subsumption 0} f#0 != null;
                assume true;
                assert {:id "id1605"} {:subsumption 0} f#0 != null;
                assert {:id "id1606"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, f#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, f#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int)
            {
                assert {:id "id1607"} {:subsumption 0} f#0 != null;
                assume true;
                assert {:id "id1608"} {:subsumption 0} f#0 != null;
                assert {:id "id1609"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            if ($Unbox(read($Heap, f#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, f#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int
               && $Unbox(read($Heap, f#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.score)): int)
            {
                assert {:id "id1610"} {:subsumption 0} f#0 != null;
                assume true;
                assert {:id "id1611"} {:subsumption 0} f#0 != null;
                assert {:id "id1612"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
                assume true;
            }

            assume true;
            assume {:id "id1613"} $Unbox(read($Heap, f#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, f#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int
               && $Unbox(read($Heap, f#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.score)): int
               && $Unbox(read($Heap, f#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
            assume true;
            assume false;
        }

        assume true;
        if (n#0 <= i#0)
        {
            break;
        }

        assume true;
        $decr$loop#00 := n#0 - i#0;
        // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(176,13)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        a##0_0 := a#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        b##0_0 := b#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        c##0_0 := c#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        d##0_0 := d#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        e##0_0 := e#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        f##0_0 := f#0;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assert {:id "id1618"} (forall $o: ref, $f: Field :: 
          $o != null
               && $Unbox(read($Heap, $o, alloc)): bool
               && (
                $o == a##0_0
                 || $o == b##0_0
                 || $o == c##0_0
                 || $o == d##0_0
                 || $o == e##0_0
                 || $o == f##0_0)
             ==> $_ModifiesFrame[$o, $f]);
        call {:id "id1619"} Call$$_module.__default.QuadBump(a##0_0, b##0_0, c##0_0, d##0_0, e##0_0, f##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "Test/arith.dfy(176,30)"} true;
        // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(177,7)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "Test/arith.dfy(177,14)"} true;
        assume true;
        // ----- loop termination check ----- /Users/saline/development/projects/dafny/Test/arith.dfy(167,3)
        assert {:id "id1621"} 0 <= $decr$loop#00 || n#0 - i#0 == $decr$loop#00;
        assert {:id "id1622"} n#0 - i#0 < $decr$loop#00;
        assume true;
    }
}



procedure {:verboseName "StressTest (well-formedness)"} CheckWellFormed$$_module.__default.StressTest(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Node()) && $IsAlloc(p#0, Tclass._module.Node(), $Heap), 
    q#0: ref
       where $Is(q#0, Tclass._module.Node()) && $IsAlloc(q#0, Tclass._module.Node(), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass._module.Node()) && $IsAlloc(r#0, Tclass._module.Node(), $Heap), 
    s#0: ref
       where $Is(s#0, Tclass._module.Node()) && $IsAlloc(s#0, Tclass._module.Node(), $Heap), 
    t#0: ref
       where $Is(t#0, Tclass._module.Node()) && $IsAlloc(t#0, Tclass._module.Node(), $Heap), 
    u#0: ref
       where $Is(u#0, Tclass._module.Node()) && $IsAlloc(u#0, Tclass._module.Node(), $Heap), 
    m#0: int, 
    n#0: int);
  modifies $Heap;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "StressTest (well-formedness)"} CheckWellFormed$$_module.__default.StressTest(a#0: ref, 
    b#0: ref, 
    c#0: ref, 
    d#0: ref, 
    e#0: ref, 
    f#0: ref, 
    p#0: ref, 
    q#0: ref, 
    r#0: ref, 
    s#0: ref, 
    t#0: ref, 
    u#0: ref, 
    m#0: int, 
    n#0: int)
{
  var $_ModifiesFrame: [ref,Field]bool;


    // AddMethodImpl: StressTest, CheckWellFormed$$_module.__default.StressTest
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool
         ==> $o == a#0
           || $o == b#0
           || $o == c#0
           || $o == d#0
           || $o == e#0
           || $o == f#0
           || $o == p#0
           || $o == q#0
           || $o == r#0
           || $o == s#0
           || $o == t#0
           || $o == u#0);
    assume {:captureState "Test/arith.dfy(190,7): initial state"} true;
    assume {:id "id1623"} m#0 >= LitInt(0);
    assume {:id "id1624"} n#0 >= LitInt(0);
    assume {:id "id1625"} a#0 != b#0;
    assume {:id "id1626"} a#0 != c#0;
    assume {:id "id1627"} a#0 != d#0;
    assume {:id "id1628"} a#0 != e#0;
    assume {:id "id1629"} a#0 != f#0;
    assume {:id "id1630"} b#0 != c#0;
    assume {:id "id1631"} b#0 != d#0;
    assume {:id "id1632"} b#0 != e#0;
    assume {:id "id1633"} b#0 != f#0;
    assume {:id "id1634"} c#0 != d#0;
    assume {:id "id1635"} c#0 != e#0;
    assume {:id "id1636"} c#0 != f#0;
    assume {:id "id1637"} d#0 != e#0;
    assume {:id "id1638"} d#0 != f#0;
    assume {:id "id1639"} e#0 != f#0;
    assume {:id "id1640"} p#0 != q#0;
    assume {:id "id1641"} p#0 != r#0;
    assume {:id "id1642"} p#0 != s#0;
    assume {:id "id1643"} p#0 != t#0;
    assume {:id "id1644"} p#0 != u#0;
    assume {:id "id1645"} q#0 != r#0;
    assume {:id "id1646"} q#0 != s#0;
    assume {:id "id1647"} q#0 != t#0;
    assume {:id "id1648"} q#0 != u#0;
    assume {:id "id1649"} r#0 != s#0;
    assume {:id "id1650"} r#0 != t#0;
    assume {:id "id1651"} r#0 != u#0;
    assume {:id "id1652"} s#0 != t#0;
    assume {:id "id1653"} s#0 != u#0;
    assume {:id "id1654"} t#0 != u#0;
    assume {:id "id1655"} a#0 != p#0;
    assume {:id "id1656"} a#0 != q#0;
    assume {:id "id1657"} a#0 != r#0;
    assume {:id "id1658"} a#0 != s#0;
    assume {:id "id1659"} a#0 != t#0;
    assume {:id "id1660"} a#0 != u#0;
    assume {:id "id1661"} b#0 != p#0;
    assume {:id "id1662"} b#0 != q#0;
    assume {:id "id1663"} b#0 != r#0;
    assume {:id "id1664"} b#0 != s#0;
    assume {:id "id1665"} b#0 != t#0;
    assume {:id "id1666"} b#0 != u#0;
    assume {:id "id1667"} c#0 != p#0;
    assume {:id "id1668"} c#0 != q#0;
    assume {:id "id1669"} c#0 != r#0;
    assume {:id "id1670"} c#0 != s#0;
    assume {:id "id1671"} c#0 != t#0;
    assume {:id "id1672"} c#0 != u#0;
    assume {:id "id1673"} d#0 != p#0;
    assume {:id "id1674"} d#0 != q#0;
    assume {:id "id1675"} d#0 != r#0;
    assume {:id "id1676"} d#0 != s#0;
    assume {:id "id1677"} d#0 != t#0;
    assume {:id "id1678"} d#0 != u#0;
    assume {:id "id1679"} e#0 != p#0;
    assume {:id "id1680"} e#0 != q#0;
    assume {:id "id1681"} e#0 != r#0;
    assume {:id "id1682"} e#0 != s#0;
    assume {:id "id1683"} e#0 != t#0;
    assume {:id "id1684"} e#0 != u#0;
    assume {:id "id1685"} f#0 != p#0;
    assume {:id "id1686"} f#0 != q#0;
    assume {:id "id1687"} f#0 != r#0;
    assume {:id "id1688"} f#0 != s#0;
    assume {:id "id1689"} f#0 != t#0;
    assume {:id "id1690"} f#0 != u#0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
         ==> $Heap[$o] == old($Heap)[$o]
           || 
          $o == a#0
           || $o == b#0
           || $o == c#0
           || $o == d#0
           || $o == e#0
           || $o == f#0
           || $o == p#0
           || $o == q#0
           || $o == r#0
           || $o == s#0
           || $o == t#0
           || $o == u#0);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "Test/arith.dfy(214,96): post-state"} true;
    assert {:id "id1691"} a#0 != null;
    assume true;
    assert {:id "id1692"} a#0 != null;
    assert {:id "id1693"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1694"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int
         + Mul(LitInt(2), m#0)
         + Mul(LitInt(4), n#0)
         + 9;
    assert {:id "id1695"} a#0 != null;
    assume true;
    assert {:id "id1696"} a#0 != null;
    assert {:id "id1697"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1698"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id1699"} a#0 != null;
    assume true;
    assert {:id "id1700"} a#0 != null;
    assert {:id "id1701"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1702"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id1703"} a#0 != null;
    assume true;
    assert {:id "id1704"} a#0 != null;
    assert {:id "id1705"} $IsAlloc(a#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1706"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
    assert {:id "id1707"} b#0 != null;
    assume true;
    assert {:id "id1708"} b#0 != null;
    assert {:id "id1709"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1710"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int
         + Mul(LitInt(2), m#0)
         + Mul(LitInt(4), n#0)
         + 9;
    assert {:id "id1711"} b#0 != null;
    assume true;
    assert {:id "id1712"} b#0 != null;
    assert {:id "id1713"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1714"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id1715"} b#0 != null;
    assume true;
    assert {:id "id1716"} b#0 != null;
    assert {:id "id1717"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1718"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id1719"} b#0 != null;
    assume true;
    assert {:id "id1720"} b#0 != null;
    assert {:id "id1721"} $IsAlloc(b#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1722"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
    assert {:id "id1723"} c#0 != null;
    assume true;
    assert {:id "id1724"} c#0 != null;
    assert {:id "id1725"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1726"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int
         + Mul(LitInt(2), m#0)
         + Mul(LitInt(4), n#0)
         + 9;
    assert {:id "id1727"} c#0 != null;
    assume true;
    assert {:id "id1728"} c#0 != null;
    assert {:id "id1729"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1730"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id1731"} c#0 != null;
    assume true;
    assert {:id "id1732"} c#0 != null;
    assert {:id "id1733"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1734"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id1735"} c#0 != null;
    assume true;
    assert {:id "id1736"} c#0 != null;
    assert {:id "id1737"} $IsAlloc(c#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1738"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
    assert {:id "id1739"} d#0 != null;
    assume true;
    assert {:id "id1740"} d#0 != null;
    assert {:id "id1741"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1742"} $Unbox(read($Heap, d#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.val)): int
         + Mul(LitInt(2), m#0)
         + Mul(LitInt(4), n#0)
         + 8;
    assert {:id "id1743"} d#0 != null;
    assume true;
    assert {:id "id1744"} d#0 != null;
    assert {:id "id1745"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1746"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
    assert {:id "id1747"} d#0 != null;
    assume true;
    assert {:id "id1748"} d#0 != null;
    assert {:id "id1749"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1750"} $Unbox(read($Heap, d#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
    assert {:id "id1751"} d#0 != null;
    assume true;
    assert {:id "id1752"} d#0 != null;
    assert {:id "id1753"} $IsAlloc(d#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1754"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
    assert {:id "id1755"} e#0 != null;
    assume true;
    assert {:id "id1756"} e#0 != null;
    assert {:id "id1757"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1758"} $Unbox(read($Heap, e#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.val)): int
         + Mul(LitInt(2), m#0)
         + Mul(LitInt(4), n#0)
         + 8;
    assert {:id "id1759"} e#0 != null;
    assume true;
    assert {:id "id1760"} e#0 != null;
    assert {:id "id1761"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1762"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
    assert {:id "id1763"} e#0 != null;
    assume true;
    assert {:id "id1764"} e#0 != null;
    assert {:id "id1765"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1766"} $Unbox(read($Heap, e#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
    assert {:id "id1767"} e#0 != null;
    assume true;
    assert {:id "id1768"} e#0 != null;
    assert {:id "id1769"} $IsAlloc(e#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1770"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
    assert {:id "id1771"} f#0 != null;
    assume true;
    assert {:id "id1772"} f#0 != null;
    assert {:id "id1773"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1774"} $Unbox(read($Heap, f#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.val)): int
         + Mul(LitInt(2), m#0)
         + Mul(LitInt(4), n#0)
         + 8;
    assert {:id "id1775"} f#0 != null;
    assume true;
    assert {:id "id1776"} f#0 != null;
    assert {:id "id1777"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1778"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
    assert {:id "id1779"} f#0 != null;
    assume true;
    assert {:id "id1780"} f#0 != null;
    assert {:id "id1781"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1782"} $Unbox(read($Heap, f#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
    assert {:id "id1783"} f#0 != null;
    assume true;
    assert {:id "id1784"} f#0 != null;
    assert {:id "id1785"} $IsAlloc(f#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1786"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
    assert {:id "id1787"} p#0 != null;
    assume true;
    assert {:id "id1788"} p#0 != null;
    assert {:id "id1789"} $IsAlloc(p#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1790"} $Unbox(read($Heap, p#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), p#0, _module.Node.val)): int + 5;
    assert {:id "id1791"} p#0 != null;
    assume true;
    assert {:id "id1792"} p#0 != null;
    assert {:id "id1793"} $IsAlloc(p#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1794"} $Unbox(read($Heap, p#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), p#0, _module.Node.tag)): int;
    assert {:id "id1795"} p#0 != null;
    assume true;
    assert {:id "id1796"} p#0 != null;
    assert {:id "id1797"} $IsAlloc(p#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1798"} $Unbox(read($Heap, p#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), p#0, _module.Node.score)): int;
    assert {:id "id1799"} p#0 != null;
    assume true;
    assert {:id "id1800"} p#0 != null;
    assert {:id "id1801"} $IsAlloc(p#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1802"} $Unbox(read($Heap, p#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), p#0, _module.Node.rank)): int;
    assert {:id "id1803"} q#0 != null;
    assume true;
    assert {:id "id1804"} q#0 != null;
    assert {:id "id1805"} $IsAlloc(q#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1806"} $Unbox(read($Heap, q#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), q#0, _module.Node.val)): int + 5;
    assert {:id "id1807"} q#0 != null;
    assume true;
    assert {:id "id1808"} q#0 != null;
    assert {:id "id1809"} $IsAlloc(q#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1810"} $Unbox(read($Heap, q#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), q#0, _module.Node.tag)): int;
    assert {:id "id1811"} q#0 != null;
    assume true;
    assert {:id "id1812"} q#0 != null;
    assert {:id "id1813"} $IsAlloc(q#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1814"} $Unbox(read($Heap, q#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), q#0, _module.Node.score)): int;
    assert {:id "id1815"} q#0 != null;
    assume true;
    assert {:id "id1816"} q#0 != null;
    assert {:id "id1817"} $IsAlloc(q#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1818"} $Unbox(read($Heap, q#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), q#0, _module.Node.rank)): int;
    assert {:id "id1819"} r#0 != null;
    assume true;
    assert {:id "id1820"} r#0 != null;
    assert {:id "id1821"} $IsAlloc(r#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1822"} $Unbox(read($Heap, r#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), r#0, _module.Node.val)): int + 5;
    assert {:id "id1823"} r#0 != null;
    assume true;
    assert {:id "id1824"} r#0 != null;
    assert {:id "id1825"} $IsAlloc(r#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1826"} $Unbox(read($Heap, r#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), r#0, _module.Node.tag)): int;
    assert {:id "id1827"} r#0 != null;
    assume true;
    assert {:id "id1828"} r#0 != null;
    assert {:id "id1829"} $IsAlloc(r#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1830"} $Unbox(read($Heap, r#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), r#0, _module.Node.score)): int;
    assert {:id "id1831"} r#0 != null;
    assume true;
    assert {:id "id1832"} r#0 != null;
    assert {:id "id1833"} $IsAlloc(r#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1834"} $Unbox(read($Heap, r#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), r#0, _module.Node.rank)): int;
    assert {:id "id1835"} s#0 != null;
    assume true;
    assert {:id "id1836"} s#0 != null;
    assert {:id "id1837"} $IsAlloc(s#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1838"} $Unbox(read($Heap, s#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), s#0, _module.Node.val)): int + 4;
    assert {:id "id1839"} s#0 != null;
    assume true;
    assert {:id "id1840"} s#0 != null;
    assert {:id "id1841"} $IsAlloc(s#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1842"} $Unbox(read($Heap, s#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), s#0, _module.Node.tag)): int;
    assert {:id "id1843"} s#0 != null;
    assume true;
    assert {:id "id1844"} s#0 != null;
    assert {:id "id1845"} $IsAlloc(s#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1846"} $Unbox(read($Heap, s#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), s#0, _module.Node.score)): int;
    assert {:id "id1847"} s#0 != null;
    assume true;
    assert {:id "id1848"} s#0 != null;
    assert {:id "id1849"} $IsAlloc(s#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1850"} $Unbox(read($Heap, s#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), s#0, _module.Node.rank)): int;
    assert {:id "id1851"} t#0 != null;
    assume true;
    assert {:id "id1852"} t#0 != null;
    assert {:id "id1853"} $IsAlloc(t#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1854"} $Unbox(read($Heap, t#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), t#0, _module.Node.val)): int + 4;
    assert {:id "id1855"} t#0 != null;
    assume true;
    assert {:id "id1856"} t#0 != null;
    assert {:id "id1857"} $IsAlloc(t#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1858"} $Unbox(read($Heap, t#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), t#0, _module.Node.tag)): int;
    assert {:id "id1859"} t#0 != null;
    assume true;
    assert {:id "id1860"} t#0 != null;
    assert {:id "id1861"} $IsAlloc(t#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1862"} $Unbox(read($Heap, t#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), t#0, _module.Node.score)): int;
    assert {:id "id1863"} t#0 != null;
    assume true;
    assert {:id "id1864"} t#0 != null;
    assert {:id "id1865"} $IsAlloc(t#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1866"} $Unbox(read($Heap, t#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), t#0, _module.Node.rank)): int;
    assert {:id "id1867"} u#0 != null;
    assume true;
    assert {:id "id1868"} u#0 != null;
    assert {:id "id1869"} $IsAlloc(u#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1870"} $Unbox(read($Heap, u#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), u#0, _module.Node.val)): int + 4;
    assert {:id "id1871"} u#0 != null;
    assume true;
    assert {:id "id1872"} u#0 != null;
    assert {:id "id1873"} $IsAlloc(u#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1874"} $Unbox(read($Heap, u#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), u#0, _module.Node.tag)): int;
    assert {:id "id1875"} u#0 != null;
    assume true;
    assert {:id "id1876"} u#0 != null;
    assert {:id "id1877"} $IsAlloc(u#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1878"} $Unbox(read($Heap, u#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), u#0, _module.Node.score)): int;
    assert {:id "id1879"} u#0 != null;
    assume true;
    assert {:id "id1880"} u#0 != null;
    assert {:id "id1881"} $IsAlloc(u#0, Tclass._module.Node(), old($Heap));
    assume true;
    assume {:id "id1882"} $Unbox(read($Heap, u#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), u#0, _module.Node.rank)): int;
}



procedure {:verboseName "StressTest (call)"} Call$$_module.__default.StressTest(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Node()) && $IsAlloc(p#0, Tclass._module.Node(), $Heap), 
    q#0: ref
       where $Is(q#0, Tclass._module.Node()) && $IsAlloc(q#0, Tclass._module.Node(), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass._module.Node()) && $IsAlloc(r#0, Tclass._module.Node(), $Heap), 
    s#0: ref
       where $Is(s#0, Tclass._module.Node()) && $IsAlloc(s#0, Tclass._module.Node(), $Heap), 
    t#0: ref
       where $Is(t#0, Tclass._module.Node()) && $IsAlloc(t#0, Tclass._module.Node(), $Heap), 
    u#0: ref
       where $Is(u#0, Tclass._module.Node()) && $IsAlloc(u#0, Tclass._module.Node(), $Heap), 
    m#0: int, 
    n#0: int);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id1883"} m#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id1884"} n#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id1885"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id1886"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1887"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1888"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1889"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1890"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1891"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1892"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1893"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1894"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1895"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1896"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1897"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1898"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1899"} e#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1900"} p#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1901"} p#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1902"} p#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1903"} p#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1904"} p#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1905"} q#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1906"} q#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1907"} q#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1908"} q#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1909"} r#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1910"} r#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1911"} r#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1912"} s#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1913"} s#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1914"} t#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1915"} a#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1916"} a#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1917"} a#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1918"} a#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1919"} a#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1920"} a#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1921"} b#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1922"} b#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1923"} b#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1924"} b#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1925"} b#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1926"} b#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1927"} c#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1928"} c#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1929"} c#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1930"} c#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1931"} c#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1932"} c#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1933"} d#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1934"} d#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1935"} d#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1936"} d#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1937"} d#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1938"} d#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1939"} e#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1940"} e#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1941"} e#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1942"} e#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1943"} e#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1944"} e#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1945"} f#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1946"} f#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1947"} f#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1948"} f#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1949"} f#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1950"} f#0 != u#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id1951"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 9;
  free ensures {:always_assume} true;
  ensures {:id "id1952"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1953"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1954"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1955"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 9;
  free ensures {:always_assume} true;
  ensures {:id "id1956"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1957"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1958"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1959"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 9;
  free ensures {:always_assume} true;
  ensures {:id "id1960"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1961"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1962"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1963"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 8;
  free ensures {:always_assume} true;
  ensures {:id "id1964"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1965"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1966"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1967"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 8;
  free ensures {:always_assume} true;
  ensures {:id "id1968"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1969"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1970"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1971"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 8;
  free ensures {:always_assume} true;
  ensures {:id "id1972"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1973"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1974"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1975"} $Unbox(read($Heap, p#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.val)): int + 5;
  free ensures {:always_assume} true;
  ensures {:id "id1976"} $Unbox(read($Heap, p#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1977"} $Unbox(read($Heap, p#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1978"} $Unbox(read($Heap, p#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1979"} $Unbox(read($Heap, q#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.val)): int + 5;
  free ensures {:always_assume} true;
  ensures {:id "id1980"} $Unbox(read($Heap, q#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1981"} $Unbox(read($Heap, q#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1982"} $Unbox(read($Heap, q#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1983"} $Unbox(read($Heap, r#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.val)): int + 5;
  free ensures {:always_assume} true;
  ensures {:id "id1984"} $Unbox(read($Heap, r#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1985"} $Unbox(read($Heap, r#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1986"} $Unbox(read($Heap, r#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1987"} $Unbox(read($Heap, s#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id1988"} $Unbox(read($Heap, s#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1989"} $Unbox(read($Heap, s#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1990"} $Unbox(read($Heap, s#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1991"} $Unbox(read($Heap, t#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id1992"} $Unbox(read($Heap, t#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1993"} $Unbox(read($Heap, t#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1994"} $Unbox(read($Heap, t#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1995"} $Unbox(read($Heap, u#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id1996"} $Unbox(read($Heap, u#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1997"} $Unbox(read($Heap, u#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1998"} $Unbox(read($Heap, u#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.rank)): int;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == a#0
         || $o == b#0
         || $o == c#0
         || $o == d#0
         || $o == e#0
         || $o == f#0
         || $o == p#0
         || $o == q#0
         || $o == r#0
         || $o == s#0
         || $o == t#0
         || $o == u#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "StressTest (correctness)"} Impl$$_module.__default.StressTest(a#0: ref
       where $Is(a#0, Tclass._module.Node()) && $IsAlloc(a#0, Tclass._module.Node(), $Heap), 
    b#0: ref
       where $Is(b#0, Tclass._module.Node()) && $IsAlloc(b#0, Tclass._module.Node(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.Node()) && $IsAlloc(c#0, Tclass._module.Node(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.Node()) && $IsAlloc(d#0, Tclass._module.Node(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass._module.Node()) && $IsAlloc(e#0, Tclass._module.Node(), $Heap), 
    f#0: ref
       where $Is(f#0, Tclass._module.Node()) && $IsAlloc(f#0, Tclass._module.Node(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Node()) && $IsAlloc(p#0, Tclass._module.Node(), $Heap), 
    q#0: ref
       where $Is(q#0, Tclass._module.Node()) && $IsAlloc(q#0, Tclass._module.Node(), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass._module.Node()) && $IsAlloc(r#0, Tclass._module.Node(), $Heap), 
    s#0: ref
       where $Is(s#0, Tclass._module.Node()) && $IsAlloc(s#0, Tclass._module.Node(), $Heap), 
    t#0: ref
       where $Is(t#0, Tclass._module.Node()) && $IsAlloc(t#0, Tclass._module.Node(), $Heap), 
    u#0: ref
       where $Is(u#0, Tclass._module.Node()) && $IsAlloc(u#0, Tclass._module.Node(), $Heap), 
    m#0: int, 
    n#0: int)
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id1999"} m#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id2000"} n#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id2001"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id2002"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id2003"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id2004"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id2005"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id2006"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id2007"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id2008"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id2009"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id2010"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id2011"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id2012"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id2013"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id2014"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id2015"} e#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id2016"} p#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id2017"} p#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id2018"} p#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id2019"} p#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2020"} p#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2021"} q#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id2022"} q#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id2023"} q#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2024"} q#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2025"} r#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id2026"} r#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2027"} r#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2028"} s#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2029"} s#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2030"} t#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2031"} a#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id2032"} a#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id2033"} a#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id2034"} a#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id2035"} a#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2036"} a#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2037"} b#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id2038"} b#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id2039"} b#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id2040"} b#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id2041"} b#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2042"} b#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2043"} c#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id2044"} c#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id2045"} c#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id2046"} c#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id2047"} c#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2048"} c#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2049"} d#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id2050"} d#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id2051"} d#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id2052"} d#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id2053"} d#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2054"} d#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2055"} e#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id2056"} e#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id2057"} e#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id2058"} e#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id2059"} e#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2060"} e#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2061"} f#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id2062"} f#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id2063"} f#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id2064"} f#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id2065"} f#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2066"} f#0 != u#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id2067"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 9;
  free ensures {:always_assume} true;
  ensures {:id "id2068"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2069"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2070"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2071"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 9;
  free ensures {:always_assume} true;
  ensures {:id "id2072"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2073"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2074"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2075"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 9;
  free ensures {:always_assume} true;
  ensures {:id "id2076"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2077"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2078"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2079"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 8;
  free ensures {:always_assume} true;
  ensures {:id "id2080"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2081"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2082"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2083"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 8;
  free ensures {:always_assume} true;
  ensures {:id "id2084"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2085"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2086"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2087"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 8;
  free ensures {:always_assume} true;
  ensures {:id "id2088"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2089"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2090"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2091"} $Unbox(read($Heap, p#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.val)): int + 5;
  free ensures {:always_assume} true;
  ensures {:id "id2092"} $Unbox(read($Heap, p#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2093"} $Unbox(read($Heap, p#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2094"} $Unbox(read($Heap, p#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2095"} $Unbox(read($Heap, q#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.val)): int + 5;
  free ensures {:always_assume} true;
  ensures {:id "id2096"} $Unbox(read($Heap, q#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2097"} $Unbox(read($Heap, q#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2098"} $Unbox(read($Heap, q#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2099"} $Unbox(read($Heap, r#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.val)): int + 5;
  free ensures {:always_assume} true;
  ensures {:id "id2100"} $Unbox(read($Heap, r#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2101"} $Unbox(read($Heap, r#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2102"} $Unbox(read($Heap, r#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2103"} $Unbox(read($Heap, s#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id2104"} $Unbox(read($Heap, s#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2105"} $Unbox(read($Heap, s#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2106"} $Unbox(read($Heap, s#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2107"} $Unbox(read($Heap, t#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id2108"} $Unbox(read($Heap, t#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2109"} $Unbox(read($Heap, t#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2110"} $Unbox(read($Heap, t#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2111"} $Unbox(read($Heap, u#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id2112"} $Unbox(read($Heap, u#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2113"} $Unbox(read($Heap, u#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2114"} $Unbox(read($Heap, u#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.rank)): int;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == a#0
         || $o == b#0
         || $o == c#0
         || $o == d#0
         || $o == e#0
         || $o == f#0
         || $o == p#0
         || $o == q#0
         || $o == r#0
         || $o == s#0
         || $o == t#0
         || $o == u#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "StressTest (correctness)"} Impl$$_module.__default.StressTest(a#0: ref, 
    b#0: ref, 
    c#0: ref, 
    d#0: ref, 
    e#0: ref, 
    f#0: ref, 
    p#0: ref, 
    q#0: ref, 
    r#0: ref, 
    s#0: ref, 
    t#0: ref, 
    u#0: ref, 
    m#0: int, 
    n#0: int)
   returns ($_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var a##0: ref;
  var b##0: ref;
  var c##0: ref;
  var d##0: ref;
  var e##0: ref;
  var f##0: ref;
  var n##0: int;
  var a##1: ref;
  var b##1: ref;
  var c##1: ref;
  var d##1: ref;
  var e##1: ref;
  var f##1: ref;
  var n##1: int;
  var a##2: ref;
  var b##2: ref;
  var c##2: ref;
  var d##2: ref;
  var e##2: ref;
  var f##2: ref;
  var a##3: ref;
  var b##3: ref;
  var c##3: ref;
  var p##0: ref;
  var q##0: ref;
  var r##0: ref;
  var a##4: ref;
  var b##4: ref;
  var c##4: ref;
  var d##3: ref;
  var e##3: ref;
  var f##3: ref;

    // AddMethodImpl: StressTest, Impl$$_module.__default.StressTest
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool
         ==> $o == a#0
           || $o == b#0
           || $o == c#0
           || $o == d#0
           || $o == e#0
           || $o == f#0
           || $o == p#0
           || $o == q#0
           || $o == r#0
           || $o == s#0
           || $o == t#0
           || $o == u#0);
    assume {:captureState "Test/arith.dfy(229,0): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(230,8)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := a#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##0 := b#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##0 := c#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##0 := d#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    e##0 := e#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    f##0 := f#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    n##0 := m#0;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id2115"} (forall $o: ref, $f: Field :: 
      $o != null
           && $Unbox(read($Heap, $o, alloc)): bool
           && (
            $o == a##0
             || $o == b##0
             || $o == c##0
             || $o == d##0
             || $o == e##0
             || $o == f##0)
         ==> $_ModifiesFrame[$o, $f]);
    call {:id "id2116"} Call$$_module.__default.BumpN(a##0, b##0, c##0, d##0, e##0, f##0, n##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(230,28)"} true;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(231,12)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##1 := a#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##1 := b#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##1 := c#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##1 := d#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    e##1 := e#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    f##1 := f#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    n##1 := n#0;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id2117"} (forall $o: ref, $f: Field :: 
      $o != null
           && $Unbox(read($Heap, $o, alloc)): bool
           && (
            $o == a##1
             || $o == b##1
             || $o == c##1
             || $o == d##1
             || $o == e##1
             || $o == f##1)
         ==> $_ModifiesFrame[$o, $f]);
    call {:id "id2118"} Call$$_module.__default.BumpNQuad(a##1, b##1, c##1, d##1, e##1, f##1, n##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(231,32)"} true;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(232,11)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##2 := a#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##2 := b#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##2 := c#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##2 := d#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    e##2 := e#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    f##2 := f#0;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id2119"} (forall $o: ref, $f: Field :: 
      $o != null
           && $Unbox(read($Heap, $o, alloc)): bool
           && (
            $o == a##2
             || $o == b##2
             || $o == c##2
             || $o == d##2
             || $o == e##2
             || $o == f##2)
         ==> $_ModifiesFrame[$o, $f]);
    call {:id "id2120"} Call$$_module.__default.OctoBump(a##2, b##2, c##2, d##2, e##2, f##2);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(232,28)"} true;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(233,12)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##3 := a#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##3 := b#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##3 := c#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    p##0 := p#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    q##0 := q#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    r##0 := r#0;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id2121"} (forall $o: ref, $f: Field :: 
      $o != null
           && $Unbox(read($Heap, $o, alloc)): bool
           && (
            $o == a##3
             || $o == b##3
             || $o == c##3
             || $o == p##0
             || $o == q##0
             || $o == r##0)
         ==> $_ModifiesFrame[$o, $f]);
    call {:id "id2122"} Call$$_module.__default.CrossBump(a##3, b##3, c##3, p##0, q##0, r##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(233,29)"} true;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(234,11)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##4 := p#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##4 := q#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##4 := r#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##3 := s#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    e##3 := t#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    f##3 := u#0;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id2123"} (forall $o: ref, $f: Field :: 
      $o != null
           && $Unbox(read($Heap, $o, alloc)): bool
           && (
            $o == a##4
             || $o == b##4
             || $o == c##4
             || $o == d##3
             || $o == e##3
             || $o == f##3)
         ==> $_ModifiesFrame[$o, $f]);
    call {:id "id2124"} Call$$_module.__default.QuadBump(a##4, b##4, c##4, d##3, e##3, f##3);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(234,28)"} true;
}



const unique class._module.Node?: ClassName;

function Tclass._module.Node?() : Ty
uses {
// Tclass._module.Node? Tag
axiom Tag(Tclass._module.Node?()) == Tagclass._module.Node?
   && TagFamily(Tclass._module.Node?()) == tytagFamily$Node;
}

const unique Tagclass._module.Node?: TyTag;

// Box/unbox axiom for Tclass._module.Node?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Node?()) } 
  $IsBox(bx, Tclass._module.Node?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Node?()));

// $Is axiom for class Node
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Node?()) } 
  $Is($o, Tclass._module.Node?())
     <==> $o == null || dtype($o) == Tclass._module.Node?());

// $IsAlloc axiom for class Node
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Node?(), $h) } 
  $IsAlloc($o, Tclass._module.Node?(), $h)
     <==> $o == null || $Unbox(read($h, $o, alloc)): bool);

const _module.Node.val: Field
uses {
axiom FDim(_module.Node.val) == 0
   && FieldOfDecl(class._module.Node?, field$val) == _module.Node.val
   && !$IsGhostField(_module.Node.val);
}

// Node.val: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.Node.val)): int } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is($Unbox(read($h, $o, _module.Node.val)): int, TInt));

// Node.val: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.Node.val)): int } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && $Unbox(read($h, $o, alloc)): bool
     ==> $IsAlloc($Unbox(read($h, $o, _module.Node.val)): int, TInt, $h));

const _module.Node.tag: Field
uses {
axiom FDim(_module.Node.tag) == 0
   && FieldOfDecl(class._module.Node?, field$tag) == _module.Node.tag
   && !$IsGhostField(_module.Node.tag);
}

// Node.tag: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.Node.tag)): int } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is($Unbox(read($h, $o, _module.Node.tag)): int, TInt));

// Node.tag: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.Node.tag)): int } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && $Unbox(read($h, $o, alloc)): bool
     ==> $IsAlloc($Unbox(read($h, $o, _module.Node.tag)): int, TInt, $h));

const _module.Node.score: Field
uses {
axiom FDim(_module.Node.score) == 0
   && FieldOfDecl(class._module.Node?, field$score) == _module.Node.score
   && !$IsGhostField(_module.Node.score);
}

// Node.score: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.Node.score)): int } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is($Unbox(read($h, $o, _module.Node.score)): int, TInt));

// Node.score: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.Node.score)): int } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && $Unbox(read($h, $o, alloc)): bool
     ==> $IsAlloc($Unbox(read($h, $o, _module.Node.score)): int, TInt, $h));

const _module.Node.rank: Field
uses {
axiom FDim(_module.Node.rank) == 0
   && FieldOfDecl(class._module.Node?, field$rank) == _module.Node.rank
   && !$IsGhostField(_module.Node.rank);
}

// Node.rank: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.Node.rank)): int } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is($Unbox(read($h, $o, _module.Node.rank)): int, TInt));

// Node.rank: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.Node.rank)): int } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && $Unbox(read($h, $o, alloc)): bool
     ==> $IsAlloc($Unbox(read($h, $o, _module.Node.rank)): int, TInt, $h));

procedure {:verboseName "Node._ctor (well-formedness)"} CheckWellFormed$$_module.Node.__ctor(v#0: int, t#0: int, s#0: int, r#0: int) returns (this: ref);
  modifies $Heap;



procedure {:verboseName "Node._ctor (call)"} Call$$_module.Node.__ctor(v#0: int, t#0: int, s#0: int, r#0: int)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap));
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id2129"} $Unbox(read($Heap, this, _module.Node.val)): int == v#0;
  free ensures {:always_assume} true;
  ensures {:id "id2130"} $Unbox(read($Heap, this, _module.Node.tag)): int == t#0;
  free ensures {:always_assume} true;
  ensures {:id "id2131"} $Unbox(read($Heap, this, _module.Node.score)): int == s#0;
  free ensures {:always_assume} true;
  ensures {:id "id2132"} $Unbox(read($Heap, this, _module.Node.rank)): int == r#0;
  // constructor allocates the object
  ensures !$Unbox(read(old($Heap), this, alloc)): bool;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "Node._ctor (correctness)"} Impl$$_module.Node.__ctor(v#0: int, t#0: int, s#0: int, r#0: int)
   returns (this: ref, $_reverifyPost: bool);
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id2133"} $Unbox(read($Heap, this, _module.Node.val)): int == v#0;
  free ensures {:always_assume} true;
  ensures {:id "id2134"} $Unbox(read($Heap, this, _module.Node.tag)): int == t#0;
  free ensures {:always_assume} true;
  ensures {:id "id2135"} $Unbox(read($Heap, this, _module.Node.score)): int == s#0;
  free ensures {:always_assume} true;
  ensures {:id "id2136"} $Unbox(read($Heap, this, _module.Node.rank)): int == r#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Node._ctor (correctness)"} Impl$$_module.Node.__ctor(v#0: int, t#0: int, s#0: int, r#0: int)
   returns (this: ref, $_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var this.val: int;
  var this.tag: int;
  var this.score: int;
  var this.rank: int;

    // AddMethodImpl: _ctor, Impl$$_module.Node.__ctor
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> false);
    assume {:captureState "Test/arith.dfy(10,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/saline/development/projects/dafny/Test/arith.dfy(10,3)
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(10,9)
    assume true;
    assume true;
    assume true;
    this.val := v#0;
    assume {:captureState "Test/arith.dfy(10,12)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(10,19)
    assume true;
    assume true;
    assume true;
    this.tag := t#0;
    assume {:captureState "Test/arith.dfy(10,22)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(10,31)
    assume true;
    assume true;
    assume true;
    this.score := s#0;
    assume {:captureState "Test/arith.dfy(10,34)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(10,42)
    assume true;
    assume true;
    assume true;
    this.rank := r#0;
    assume {:captureState "Test/arith.dfy(10,45)"} true;
    // ----- new; ----- /Users/saline/development/projects/dafny/Test/arith.dfy(10,3)
    assume this != null && $Is(this, Tclass._module.Node?());
    assume !$Unbox(read($Heap, this, alloc)): bool;
    assume $Unbox(read($Heap, this, _module.Node.val)): int == this.val;
    assume $Unbox(read($Heap, this, _module.Node.tag)): int == this.tag;
    assume $Unbox(read($Heap, this, _module.Node.score)): int == this.score;
    assume $Unbox(read($Heap, this, _module.Node.rank)): int == this.rank;
    $Heap := update($Heap, this, alloc, $Box(true));
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/saline/development/projects/dafny/Test/arith.dfy(10,3)
}



// $Is axiom for non-null type _module.Node
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Node()) } { $Is(c#0, Tclass._module.Node?()) } 
  $Is(c#0, Tclass._module.Node())
     <==> $Is(c#0, Tclass._module.Node?()) && c#0 != null);

// $IsAlloc axiom for non-null type _module.Node
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Node(), $h) } 
  $IsAlloc(c#0, Tclass._module.Node(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Node?(), $h));

const unique tytagFamily$nat: TyTagFamily;

const unique tytagFamily$object: TyTagFamily;

const unique tytagFamily$array: TyTagFamily;

const unique tytagFamily$_#Func1: TyTagFamily;

const unique tytagFamily$_#PartialFunc1: TyTagFamily;

const unique tytagFamily$_#TotalFunc1: TyTagFamily;

const unique tytagFamily$_#Func0: TyTagFamily;

const unique tytagFamily$_#PartialFunc0: TyTagFamily;

const unique tytagFamily$_#TotalFunc0: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$_#Func2: TyTagFamily;

const unique tytagFamily$_#PartialFunc2: TyTagFamily;

const unique tytagFamily$_#TotalFunc2: TyTagFamily;

const unique tytagFamily$Node: TyTagFamily;

const unique field$val: NameFamily;

const unique field$tag: NameFamily;

const unique field$score: NameFamily;

const unique field$rank: NameFamily;
