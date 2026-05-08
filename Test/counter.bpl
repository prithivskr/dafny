
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

revealed function TSet(Ty) : Ty;

revealed function TISet(Ty) : Ty;

revealed function TMultiSet(Ty) : Ty;

revealed function TSeq(Ty) : Ty;

revealed function TMap(Ty, Ty) : Ty;

revealed function TIMap(Ty, Ty) : Ty;

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

axiom (forall<T> v: T, t: Ty :: 
  { $IsBox($Box(v), t) } 
  $IsBox($Box(v), t) <==> $Is(v, t));

revealed function $Is<T>(T, Ty) : bool;

axiom (forall v: int :: { $Is(v, TInt) } $Is(v, TInt));

axiom (forall v: real :: { $Is(v, TReal) } $Is(v, TReal));

axiom (forall v: bool :: { $Is(v, TBool) } $Is(v, TBool));

axiom (forall v: char :: { $Is(v, TChar) } $Is(v, TChar));

axiom (forall v: Field :: { $Is(v, TField) } $Is(v, TField));

axiom (forall v: ORDINAL :: { $Is(v, TORDINAL) } $Is(v, TORDINAL));

axiom (forall v: Bv0 :: { $Is(v, TBitvector(0)) } $Is(v, TBitvector(0)));

revealed function $IsAlloc<T>(T, Ty, Heap) : bool;

revealed function $AlwaysAllocated(Ty) : bool;

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

revealed function Apply1(Ty, Ty, Heap, HandleType, Box) : Box;

revealed function Requires0(Ty, Heap, HandleType) : bool;

revealed function Requires1(Ty, Ty, Heap, HandleType, Box) : bool;

revealed function Requires2(Ty, Ty, Ty, Heap, HandleType, Box, Box) : bool;

revealed function Reads0(Ty, Heap, HandleType) : Set;

revealed function Reads1(Ty, Ty, Heap, HandleType, Box) : Set;

revealed function Reads2(Ty, Ty, Ty, Heap, HandleType, Box, Box) : Set;

revealed function Requires0#canCall(Ty, Heap, HandleType) : bool;

revealed function Requires1#canCall(Ty, Ty, Heap, HandleType, Box) : bool;

revealed function Requires2#canCall(Ty, Ty, Ty, Heap, HandleType, Box, Box) : bool;

type DatatypeType;

type DtCtorId;

revealed function DatatypeCtorId(DatatypeType) : DtCtorId;

revealed function DtRank(DatatypeType) : int;

revealed function BoxRank(Box) : int;

axiom (forall d: DatatypeType :: { BoxRank($Box(d)) } BoxRank($Box(d)) == DtRank(d));

type ORDINAL = Box;

revealed function ORD#IsNat(ORDINAL) : bool;

revealed function ORD#Offset(ORDINAL) : int;

revealed function {:inline} ORD#IsLimit(o: ORDINAL) : bool
{
  ORD#Offset(o) == 0
}

revealed function {:inline} ORD#IsSucc(o: ORDINAL) : bool
{
  0 < ORD#Offset(o)
}

revealed function ORD#FromNat(int) : ORDINAL;

revealed function ORD#Less(ORDINAL, ORDINAL) : bool;

revealed function ORD#LessThanLimit(ORDINAL, ORDINAL) : bool;

revealed function ORD#Plus(ORDINAL, ORDINAL) : ORDINAL;

revealed function ORD#Minus(ORDINAL, ORDINAL) : ORDINAL;

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

revealed function FDim(Field) : int;

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

revealed function DeclName(Field) : NameFamily;

revealed function FieldOfDecl(ClassName, NameFamily) : Field;

axiom (forall cl: ClassName, nm: NameFamily :: 
  { FieldOfDecl(cl, nm): Field } 
  DeclType(FieldOfDecl(cl, nm): Field) == cl
     && DeclName(FieldOfDecl(cl, nm): Field) == nm);

revealed function $IsGhostField(Field) : bool;

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

var $Alloc: [ref]bool;

revealed function $IsGoodHeap(Heap) : bool;

revealed function $IsHeapAnchor(Heap) : bool;

var $Heap: Heap;

const $OneHeap: Heap;

revealed function $HeapSucc(Heap, Heap) : bool;

revealed function $HeapSuccGhost(Heap, Heap) : bool;

procedure $YieldHavoc(this: ref, rds: Set, nw: Set);
  modifies $Heap;



procedure $IterHavoc0(this: ref, rds: Set, modi: Set);
  modifies $Heap;



procedure $IterHavoc1(this: ref, modi: Set, nw: Set);
  modifies $Heap;



procedure $IterCollectNewObjects(prevHeap: Heap, newHeap: Heap, this: ref, NW: Field) returns (s: Set);



type Set;

revealed function Set#Card(s: Set) : int;

revealed function Set#Empty() : Set;

revealed function Set#IsMember(s: Set, o: Box) : bool;

revealed function Set#UnionOne(s: Set, o: Box) : Set;

revealed function Set#Union(a: Set, b: Set) : Set;

revealed function Set#Intersection(a: Set, b: Set) : Set;

revealed function Set#Difference(a: Set, b: Set) : Set;

revealed function Set#Subset(a: Set, b: Set) : bool;

revealed function Set#Equal(a: Set, b: Set) : bool;

revealed function Set#Disjoint(a: Set, b: Set) : bool;

revealed function Set#FromBoogieMap([Box]bool) : Set;

type ISet = [Box]bool;

revealed function ISet#Empty() : ISet;

revealed function ISet#FromSet(Set) : ISet;

revealed function ISet#UnionOne(ISet, Box) : ISet;

revealed function ISet#Union(ISet, ISet) : ISet;

revealed function ISet#Intersection(ISet, ISet) : ISet;

revealed function ISet#Difference(ISet, ISet) : ISet;

revealed function ISet#Subset(ISet, ISet) : bool;

revealed function ISet#Equal(ISet, ISet) : bool;

revealed function ISet#Disjoint(ISet, ISet) : bool;

revealed function Math#min(a: int, b: int) : int;

revealed function Math#clip(a: int) : int;

type MultiSet;

revealed function MultiSet#Multiplicity(m: MultiSet, o: Box) : int;

revealed function MultiSet#UpdateMultiplicity(m: MultiSet, o: Box, n: int) : MultiSet;

revealed function $IsGoodMultiSet(ms: MultiSet) : bool;

revealed function MultiSet#Card(m: MultiSet) : int;

revealed function MultiSet#Empty() : MultiSet;

revealed function MultiSet#Singleton(o: Box) : MultiSet;

revealed function MultiSet#UnionOne(m: MultiSet, o: Box) : MultiSet;

revealed function MultiSet#Union(a: MultiSet, b: MultiSet) : MultiSet;

revealed function MultiSet#Intersection(a: MultiSet, b: MultiSet) : MultiSet;

revealed function MultiSet#Difference(a: MultiSet, b: MultiSet) : MultiSet;

revealed function MultiSet#Subset(a: MultiSet, b: MultiSet) : bool;

revealed function MultiSet#Equal(a: MultiSet, b: MultiSet) : bool;

revealed function MultiSet#Disjoint(a: MultiSet, b: MultiSet) : bool;

revealed function MultiSet#FromSet(s: Set) : MultiSet;

revealed function MultiSet#FromSeq(s: Seq) : MultiSet;

type Seq;

revealed function Seq#Length(s: Seq) : int;

revealed function Seq#Empty() : Seq;

revealed function Seq#Build(s: Seq, val: Box) : Seq;

revealed function Seq#Build_inv0(s: Seq) : Seq;

revealed function Seq#Build_inv1(s: Seq) : Box;

revealed function Seq#Index(s: Seq, i: int) : Box;

revealed function Seq#Update(s: Seq, i: int, val: Box) : Seq;

revealed function Seq#Append(s0: Seq, s1: Seq) : Seq;

revealed function Seq#Contains(s: Seq, val: Box) : bool;

revealed function Seq#Equal(s0: Seq, s1: Seq) : bool;

revealed function Seq#SameUntil(s0: Seq, s1: Seq, n: int) : bool;

revealed function Seq#Take(s: Seq, howMany: int) : Seq;

revealed function Seq#Drop(s: Seq, howMany: int) : Seq;

revealed function Seq#Create(ty: Ty, heap: Heap, len: int, init: HandleType) : Seq;

revealed function Seq#FromArray(h: Heap, a: ref) : Seq;

revealed function Seq#Rank(Seq) : int;

type Map;

type IMap;

revealed function #_System._tuple#2._#Make2(Box, Box) : DatatypeType;

revealed function _System.Tuple2._0(DatatypeType) : Box;

revealed function _System.Tuple2._1(DatatypeType) : Box;

revealed function Map#Domain(Map) : Set;

revealed function Map#Elements(Map) : [Box]Box;

revealed function Map#Card(Map) : int;

revealed function Map#Values(Map) : Set;

revealed function Map#Items(Map) : Set;

revealed function Map#Empty() : Map;

revealed function Map#Glue(Set, [Box]Box, Ty) : Map;

revealed function Map#Build(Map, Box, Box) : Map;

revealed function Map#Merge(Map, Map) : Map;

revealed function Map#Subtract(Map, Set) : Map;

revealed function Map#Equal(Map, Map) : bool;

revealed function Map#Disjoint(Map, Map) : bool;

revealed function IMap#Domain(IMap) : ISet;

revealed function IMap#Elements(IMap) : [Box]Box;

revealed function IMap#Values(IMap) : ISet;

revealed function IMap#Items(IMap) : ISet;

revealed function IMap#Empty() : IMap;

revealed function IMap#Glue([Box]bool, [Box]Box, Ty) : IMap;

revealed function IMap#Build(IMap, Box, Box) : IMap;

revealed function IMap#Equal(IMap, IMap) : bool;

revealed function IMap#Merge(IMap, IMap) : IMap;

revealed function IMap#Subtract(IMap, Set) : IMap;

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

// $Is axiom for array type array
axiom (forall _System.array$arg: Ty, $o: ref :: 
  { $Is($o, Tclass._System.array?(_System.array$arg)) } 
  $Is($o, Tclass._System.array?(_System.array$arg))
     <==> $o == null || dtype($o) == Tclass._System.array?(_System.array$arg));

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

const unique class._module.__default: ClassName;

function Tclass._module.Cell() : Ty
uses {
// Tclass._module.Cell Tag
axiom Tag(Tclass._module.Cell()) == Tagclass._module.Cell
   && TagFamily(Tclass._module.Cell()) == tytagFamily$Cell;
}

const unique Tagclass._module.Cell: TyTag;

// Box/unbox axiom for Tclass._module.Cell
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Cell()) } 
  $IsBox(bx, Tclass._module.Cell())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Cell()));

procedure {:verboseName "UpdateCells (well-formedness)"} CheckWellFormed$$_module.__default.UpdateCells(a#0: ref where $Is(a#0, Tclass._module.Cell()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Cell()) && (b#0 == null || $Alloc[b#0]))
   returns (sum#0: int);
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "UpdateCells (well-formedness)"} CheckWellFormed$$_module.__default.UpdateCells(a#0: ref, b#0: ref) returns (sum#0: int)
{

    // AddMethodImpl: UpdateCells, CheckWellFormed$$_module.__default.UpdateCells
    assume {:captureState "Test/counter.dfy(25,7): initial state"} true;
    assume {:id "id0"} a#0 != b#0;
    assert {:id "id1"} a#0 != null;
    assume true;
    assume {:id "id2"} $Unbox(read($Heap, a#0, _module.Cell.value)): int >= LitInt(0);
    assert {:id "id3"} b#0 != null;
    assume true;
    assume {:id "id4"} $Unbox(read($Heap, b#0, _module.Cell.value)): int >= LitInt(0);
    havoc $Heap;
    havoc sum#0;
    assume {:captureState "Test/counter.dfy(30,18): post-state"} true;
    assert {:id "id5"} a#0 != null;
    assume true;
    assert {:id "id6"} a#0 != null;
    assert {:id "id7"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id8"} $Unbox(read($Heap, a#0, _module.Cell.value)): int
       == $Unbox(read(old($Heap), a#0, _module.Cell.value)): int + 1;
    assert {:id "id9"} b#0 != null;
    assume true;
    assert {:id "id10"} b#0 != null;
    assert {:id "id11"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id12"} $Unbox(read($Heap, b#0, _module.Cell.value)): int
       == $Unbox(read(old($Heap), b#0, _module.Cell.value)): int + 2;
    assert {:id "id13"} a#0 != null;
    assume true;
    assert {:id "id14"} b#0 != null;
    assume true;
    assume {:id "id15"} sum#0
       == $Unbox(read($Heap, a#0, _module.Cell.value)): int
         + $Unbox(read($Heap, b#0, _module.Cell.value)): int;
}



procedure {:verboseName "UpdateCells (call)"} Call$$_module.__default.UpdateCells(a#0: ref where $Is(a#0, Tclass._module.Cell()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Cell()) && (b#0 == null || $Alloc[b#0]))
   returns (sum#0: int);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id16"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id17"} $Unbox(read($Heap, a#0, _module.Cell.value)): int >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id18"} $Unbox(read($Heap, b#0, _module.Cell.value)): int >= LitInt(0);
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id19"} $Unbox(read($Heap, a#0, _module.Cell.value)): int
     == $Unbox(read(old($Heap), a#0, _module.Cell.value)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id20"} $Unbox(read($Heap, b#0, _module.Cell.value)): int
     == $Unbox(read(old($Heap), b#0, _module.Cell.value)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id21"} sum#0
     == $Unbox(read($Heap, a#0, _module.Cell.value)): int
       + $Unbox(read($Heap, b#0, _module.Cell.value)): int;



procedure {:verboseName "UpdateCells (correctness)"} Impl$$_module.__default.UpdateCells(a#0: ref where $Is(a#0, Tclass._module.Cell()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Cell()) && (b#0 == null || $Alloc[b#0]))
   returns (defass#sum#0: bool, sum#0: int, $_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id22"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id23"} $Unbox(read($Heap, a#0, _module.Cell.value)): int >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id24"} $Unbox(read($Heap, b#0, _module.Cell.value)): int >= LitInt(0);
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id25"} $Unbox(read($Heap, a#0, _module.Cell.value)): int
     == $Unbox(read(old($Heap), a#0, _module.Cell.value)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id26"} $Unbox(read($Heap, b#0, _module.Cell.value)): int
     == $Unbox(read(old($Heap), b#0, _module.Cell.value)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id27"} sum#0
     == $Unbox(read($Heap, a#0, _module.Cell.value)): int
       + $Unbox(read($Heap, b#0, _module.Cell.value)): int;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "UpdateCells (correctness)"} Impl$$_module.__default.UpdateCells(a#0: ref, b#0: ref)
   returns (defass#sum#0: bool, sum#0: int, $_reverifyPost: bool)
{
  var $PreCallHeap#0: Heap;
  var $PreCallAlloc#0: [ref]bool;
  var $rhs#0: int;

    // AddMethodImpl: UpdateCells, Impl$$_module.__default.UpdateCells
    assume {:captureState "Test/counter.dfy(33,0): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/counter.dfy(34,14)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert {:id "id28"} a#0 != null;
    $PreCallHeap#0 := $Heap;
    $PreCallAlloc#0 := $Alloc;
    assume true;
    call {:id "id29"} Call$$_module.Cell.Increment(a#0);
    // qf-call-frame Increment: supports=2 reads=2 modified=1
    assume a#0 != null && a#0 != a#0
       ==> read($Heap, a#0, _module.Cell.value)
         == read($PreCallHeap#0, a#0, _module.Cell.value);
    assume b#0 != null && b#0 != a#0
       ==> read($Heap, b#0, _module.Cell.value)
         == read($PreCallHeap#0, b#0, _module.Cell.value);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/counter.dfy(34,15)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/counter.dfy(36,11)
    assert {:id "id30"} b#0 != null;
    assume true;
    assume true;
    assert {:id "id31"} b#0 != null;
    assume true;
    assume true;
    $rhs#0 := $Unbox(read($Heap, b#0, _module.Cell.value)): int + 2;
    $Heap := update($Heap, b#0, _module.Cell.value, $Box($rhs#0));
    assume true;
    assume {:captureState "Test/counter.dfy(36,24)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/counter.dfy(38,7)
    assume true;
    assert {:id "id34"} a#0 != null;
    assume true;
    assert {:id "id35"} b#0 != null;
    assume true;
    assume true;
    sum#0 := $Unbox(read($Heap, a#0, _module.Cell.value)): int
       + $Unbox(read($Heap, b#0, _module.Cell.value)): int;
    defass#sum#0 := true;
    assume {:captureState "Test/counter.dfy(38,26)"} true;
    assert {:id "id37"} defass#sum#0;
}



procedure {:verboseName "Main (well-formedness)"} CheckWellFormed$$_module.__default.Main();
  modifies $Heap, $Alloc;



procedure {:verboseName "Main (call)"} Call$$_module.__default.Main();
  modifies $Heap, $Alloc;



procedure {:verboseName "Main (correctness)"} Impl$$_module.__default.Main() returns ($_reverifyPost: bool);
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Main (correctness)"} Impl$$_module.__default.Main() returns ($_reverifyPost: bool)
{
  var defass#x#0: bool;
  var x#0: ref
     where defass#x#0 ==> $Is(x#0, Tclass._module.Cell()) && (x#0 == null || $Alloc[x#0]);
  var $nw: ref;
  var v##0: int;
  var $PreCallHeap#0: Heap;
  var $PreCallAlloc#0: [ref]bool;
  var defass#y#0: bool;
  var y#0: ref
     where defass#y#0 ==> $Is(y#0, Tclass._module.Cell()) && (y#0 == null || $Alloc[y#0]);
  var v##1: int;
  var $PreCallHeap#1: Heap;
  var $PreCallAlloc#1: [ref]bool;
  var total#0: int;
  var $rhs##0: int;
  var a##0: ref;
  var b##0: ref;
  var $PreCallHeap#2: Heap;
  var $PreCallAlloc#2: [ref]bool;

    // AddMethodImpl: Main, Impl$$_module.__default.Main
    assume {:captureState "Test/counter.dfy(42,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/counter.dfy(43,9)
    assume true;
    // ----- init call statement ----- /Users/saline/development/projects/dafny/Test/counter.dfy(43,12)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    v##0 := LitInt(3);
    $PreCallHeap#0 := $Heap;
    $PreCallAlloc#0 := $Alloc;
    call {:id "id38"} $nw := Call$$_module.Cell.__ctor(v##0);
    assume !$PreCallAlloc#0[$nw];
    assume !old($Alloc)[$nw];
    // qf-call-frame _ctor: supports=2 reads=2 modified=1
    assume $nw != null && $nw != $nw
       ==> read($Heap, $nw, _module.Cell.value)
         == read($PreCallHeap#0, $nw, _module.Cell.value);
    assume x#0 != null && x#0 != $nw
       ==> read($Heap, x#0, _module.Cell.value)
         == read($PreCallHeap#0, x#0, _module.Cell.value);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/counter.dfy(43,22)"} true;
    x#0 := $nw;
    defass#x#0 := true;
    assume {:captureState "Test/counter.dfy(43,22)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/counter.dfy(44,9)
    assume true;
    // ----- init call statement ----- /Users/saline/development/projects/dafny/Test/counter.dfy(44,12)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    v##1 := LitInt(5);
    $PreCallHeap#1 := $Heap;
    $PreCallAlloc#1 := $Alloc;
    call {:id "id40"} $nw := Call$$_module.Cell.__ctor(v##1);
    assume !$PreCallAlloc#1[$nw];
    assume !old($Alloc)[$nw];
    // qf-call-frame _ctor: supports=3 reads=3 modified=1
    assume $nw != null && $nw != $nw
       ==> read($Heap, $nw, _module.Cell.value)
         == read($PreCallHeap#1, $nw, _module.Cell.value);
    assume x#0 != null && x#0 != $nw
       ==> read($Heap, x#0, _module.Cell.value)
         == read($PreCallHeap#1, x#0, _module.Cell.value);
    assume y#0 != null && y#0 != $nw
       ==> read($Heap, y#0, _module.Cell.value)
         == read($PreCallHeap#1, y#0, _module.Cell.value);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/counter.dfy(44,22)"} true;
    y#0 := $nw;
    defass#y#0 := true;
    assume {:captureState "Test/counter.dfy(44,22)"} true;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/counter.dfy(46,27)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assert {:id "id42"} defass#x#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := x#0;
    assert {:id "id43"} defass#y#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##0 := y#0;
    $PreCallHeap#2 := $Heap;
    $PreCallAlloc#2 := $Alloc;
    assume true;
    assume true;
    assert {:id "id44"} !old($Alloc)[a##0];
    assert {:id "id45"} !old($Alloc)[b##0];
    call {:id "id46"} $rhs##0 := Call$$_module.__default.UpdateCells(a##0, b##0);
    // qf-call-frame UpdateCells: supports=5 reads=5 modified=2
    assume x#0 != null && x#0 != x#0 && x#0 != y#0
       ==> read($Heap, x#0, _module.Cell.value)
         == read($PreCallHeap#2, x#0, _module.Cell.value);
    assume y#0 != null && y#0 != x#0 && y#0 != y#0
       ==> read($Heap, y#0, _module.Cell.value)
         == read($PreCallHeap#2, y#0, _module.Cell.value);
    assume $nw != null && $nw != x#0 && $nw != y#0
       ==> read($Heap, $nw, _module.Cell.value)
         == read($PreCallHeap#2, $nw, _module.Cell.value);
    assume a##0 != null && a##0 != x#0 && a##0 != y#0
       ==> read($Heap, a##0, _module.Cell.value)
         == read($PreCallHeap#2, a##0, _module.Cell.value);
    assume b##0 != null && b##0 != x#0 && b##0 != y#0
       ==> read($Heap, b##0, _module.Cell.value)
         == read($PreCallHeap#2, b##0, _module.Cell.value);
    // TrCallStmt: After ProcessCallStmt
    total#0 := $rhs##0;
    assume {:captureState "Test/counter.dfy(46,32)"} true;
    // ----- assert statement ----- /Users/saline/development/projects/dafny/Test/counter.dfy(48,3)
    assert {:id "id48"} defass#x#0;
    assert {:id "id49"} {:subsumption 0} x#0 != null;
    assume true;
    assume true;
    assert {:id "id50"} $Unbox(read($Heap, x#0, _module.Cell.value)): int == LitInt(4);
    // ----- assert statement ----- /Users/saline/development/projects/dafny/Test/counter.dfy(49,3)
    assert {:id "id51"} defass#y#0;
    assert {:id "id52"} {:subsumption 0} y#0 != null;
    assume true;
    assume true;
    assert {:id "id53"} $Unbox(read($Heap, y#0, _module.Cell.value)): int == LitInt(7);
    // ----- assert statement ----- /Users/saline/development/projects/dafny/Test/counter.dfy(50,3)
    assume true;
    assert {:id "id54"} total#0 == LitInt(11);
}



const unique class._module.Cell?: ClassName;

function Tclass._module.Cell?() : Ty
uses {
// Tclass._module.Cell? Tag
axiom Tag(Tclass._module.Cell?()) == Tagclass._module.Cell?
   && TagFamily(Tclass._module.Cell?()) == tytagFamily$Cell;
}

const unique Tagclass._module.Cell?: TyTag;

// Box/unbox axiom for Tclass._module.Cell?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Cell?()) } 
  $IsBox(bx, Tclass._module.Cell?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Cell?()));

// $Is axiom for class Cell
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Cell?()) } 
  $Is($o, Tclass._module.Cell?())
     <==> $o == null || dtype($o) == Tclass._module.Cell?());

const _module.Cell.value: Field
uses {
axiom FDim(_module.Cell.value) == 0
   && FieldOfDecl(class._module.Cell?, field$value) == _module.Cell.value
   && !$IsGhostField(_module.Cell.value);
}

procedure {:verboseName "Cell._ctor (well-formedness)"} CheckWellFormed$$_module.Cell.__ctor(v#0: int) returns (this: ref);
  modifies $Heap, $Alloc;



procedure {:verboseName "Cell._ctor (call)"} Call$$_module.Cell.__ctor(v#0: int)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Cell())
         && (this == null || $Alloc[this]));
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id56"} $Unbox(read($Heap, this, _module.Cell.value)): int == v#0;
  // constructor allocates the object
  ensures !old($Alloc)[this];



procedure {:verboseName "Cell._ctor (correctness)"} Impl$$_module.Cell.__ctor(v#0: int) returns (this: ref, $_reverifyPost: bool);
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id57"} $Unbox(read($Heap, this, _module.Cell.value)): int == v#0;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Cell._ctor (correctness)"} Impl$$_module.Cell.__ctor(v#0: int) returns (this: ref, $_reverifyPost: bool)
{
  var this.value: int;

    // AddMethodImpl: _ctor, Impl$$_module.Cell.__ctor
    assume {:captureState "Test/counter.dfy(6,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/saline/development/projects/dafny/Test/counter.dfy(6,3)
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/counter.dfy(7,11)
    assume true;
    assume true;
    assume true;
    this.value := v#0;
    assume {:captureState "Test/counter.dfy(7,14)"} true;
    // ----- new; ----- /Users/saline/development/projects/dafny/Test/counter.dfy(6,3)
    assume this != null && $Is(this, Tclass._module.Cell?());
    assume !$Alloc[this];
    assume $Unbox(read($Heap, this, _module.Cell.value)): int == this.value;
    $Alloc := $Alloc[this := true];
    assume true;
    // ----- divided block after new; ----- /Users/saline/development/projects/dafny/Test/counter.dfy(6,3)
}



procedure {:verboseName "Cell.SetValue (well-formedness)"} CheckWellFormed$$_module.Cell.SetValue(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Cell())
         && (this == null || $Alloc[this]), 
    v#0: int);
  modifies $Heap, $Alloc;



procedure {:verboseName "Cell.SetValue (call)"} Call$$_module.Cell.SetValue(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Cell())
         && (this == null || $Alloc[this]), 
    v#0: int);
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id60"} $Unbox(read($Heap, this, _module.Cell.value)): int == v#0;



procedure {:verboseName "Cell.SetValue (correctness)"} Impl$$_module.Cell.SetValue(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Cell())
         && (this == null || $Alloc[this]), 
    v#0: int)
   returns ($_reverifyPost: bool);
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id61"} $Unbox(read($Heap, this, _module.Cell.value)): int == v#0;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Cell.SetValue (correctness)"} Impl$$_module.Cell.SetValue(this: ref, v#0: int) returns ($_reverifyPost: bool)
{
  var $rhs#0: int;

    // AddMethodImpl: SetValue, Impl$$_module.Cell.SetValue
    assume {:captureState "Test/counter.dfy(13,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/counter.dfy(14,11)
    assume true;
    assume true;
    assume true;
    $rhs#0 := v#0;
    $Heap := update($Heap, this, _module.Cell.value, $Box($rhs#0));
    assume true;
    assume {:captureState "Test/counter.dfy(14,14)"} true;
}



procedure {:verboseName "Cell.Increment (well-formedness)"} CheckWellFormed$$_module.Cell.Increment(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Cell())
         && (this == null || $Alloc[this]));
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Cell.Increment (well-formedness)"} CheckWellFormed$$_module.Cell.Increment(this: ref)
{

    // AddMethodImpl: Increment, CheckWellFormed$$_module.Cell.Increment
    assume {:captureState "Test/counter.dfy(17,9): initial state"} true;
    havoc $Heap;
    assume {:captureState "Test/counter.dfy(19,18): post-state"} true;
    assume true;
    assert {:id "id64"} this == null || old($Alloc)[this];
    assume true;
    assume {:id "id65"} $Unbox(read($Heap, this, _module.Cell.value)): int
       == $Unbox(read(old($Heap), this, _module.Cell.value)): int + 1;
}



procedure {:verboseName "Cell.Increment (call)"} Call$$_module.Cell.Increment(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Cell())
         && (this == null || $Alloc[this]));
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id66"} $Unbox(read($Heap, this, _module.Cell.value)): int
     == $Unbox(read(old($Heap), this, _module.Cell.value)): int + 1;



procedure {:verboseName "Cell.Increment (correctness)"} Impl$$_module.Cell.Increment(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Cell())
         && (this == null || $Alloc[this]))
   returns ($_reverifyPost: bool);
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id67"} $Unbox(read($Heap, this, _module.Cell.value)): int
     == $Unbox(read(old($Heap), this, _module.Cell.value)): int + 1;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Cell.Increment (correctness)"} Impl$$_module.Cell.Increment(this: ref) returns ($_reverifyPost: bool)
{
  var $rhs#0: int;

    // AddMethodImpl: Increment, Impl$$_module.Cell.Increment
    assume {:captureState "Test/counter.dfy(20,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/counter.dfy(21,11)
    assume true;
    assume true;
    assume true;
    assume true;
    $rhs#0 := $Unbox(read($Heap, this, _module.Cell.value)): int + 1;
    $Heap := update($Heap, this, _module.Cell.value, $Box($rhs#0));
    assume true;
    assume {:captureState "Test/counter.dfy(21,22)"} true;
}



// $Is axiom for non-null type _module.Cell
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Cell()) } { $Is(c#0, Tclass._module.Cell?()) } 
  $Is(c#0, Tclass._module.Cell())
     <==> $Is(c#0, Tclass._module.Cell?()) && c#0 != null);

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

const unique tytagFamily$Cell: TyTagFamily;

const unique field$value: NameFamily;
