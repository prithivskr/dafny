
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

// function declaration for _module._default.ListLength
function _module.__default.ListLength($ly: LayerType, l#0: DatatypeType) : int;

function _module.__default.ListLength#canCall(l#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, l#0: DatatypeType :: 
  { _module.__default.ListLength($LS($ly), l#0) } 
  _module.__default.ListLength($LS($ly), l#0)
     == _module.__default.ListLength($ly, l#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, l#0: DatatypeType :: 
  { _module.__default.ListLength(AsFuelBottom($ly), l#0) } 
  _module.__default.ListLength($ly, l#0) == _module.__default.ListLength($LZ, l#0));

function Tclass._module.List() : Ty
uses {
// Tclass._module.List Tag
axiom Tag(Tclass._module.List()) == Tagclass._module.List
   && TagFamily(Tclass._module.List()) == tytagFamily$List;
}

const unique Tagclass._module.List: TyTag;

// Box/unbox axiom for Tclass._module.List
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.List()) } 
  $IsBox(bx, Tclass._module.List())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.List()));

// consequence axiom for _module.__default.ListLength
axiom (forall $ly: LayerType, l#0: DatatypeType :: 
  { _module.__default.ListLength($ly, l#0) } 
  _module.__default.ListLength#canCall(l#0)
     ==> LitInt(0) <= _module.__default.ListLength($ly, l#0));

function _module.__default.ListLength#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.ListLength
axiom (forall $ly: LayerType, l#0: DatatypeType :: 
  { _module.__default.ListLength#requires($ly, l#0) } 
  $Is(l#0, Tclass._module.List())
     ==> _module.__default.ListLength#requires($ly, l#0) == true);

// #requires ==> #canCall for _module.__default.ListLength
axiom (forall $ly: LayerType, l#0: DatatypeType :: 
  { _module.__default.ListLength#requires($ly, l#0) } 
  _module.__default.ListLength#requires($ly, l#0)
     ==> _module.__default.ListLength#canCall(l#0));

// definition axiom for _module.__default.ListLength (revealed)
axiom {:id "id0"} (forall $ly: LayerType, l#0: DatatypeType :: 
  { _module.__default.ListLength($LS($ly), l#0) } 
  _module.__default.ListLength#canCall(l#0)
     ==> (!_module.List.Nil_q(l#0)
         ==> (var t#1 := _module.List.tail(l#0); _module.__default.ListLength#canCall(t#1)))
       && _module.__default.ListLength($LS($ly), l#0)
         == (if _module.List.Nil_q(l#0)
           then 0
           else (var t#0 := _module.List.tail(l#0); 1 + _module.__default.ListLength($ly, t#0))));

// definition axiom for _module.__default.ListLength for all literals (revealed)
axiom {:id "id1"} (forall $ly: LayerType, l#0: DatatypeType :: 
  {:weight 3} { _module.__default.ListLength($LS($ly), Lit(l#0)) } 
  _module.__default.ListLength#canCall(Lit(l#0))
     ==> (!Lit(_module.List.Nil_q(Lit(l#0)))
         ==> (var t#3 := Lit(_module.List.tail(Lit(l#0))); 
          _module.__default.ListLength#canCall(t#3)))
       && _module.__default.ListLength($LS($ly), Lit(l#0))
         == (if _module.List.Nil_q(Lit(l#0))
           then 0
           else (var t#2 := Lit(_module.List.tail(Lit(l#0))); 
            LitInt(1 + _module.__default.ListLength($LS($ly), t#2)))));

procedure {:verboseName "ListLength (well-formedness)"} CheckWellformed$$_module.__default.ListLength(l#0: DatatypeType where $Is(l#0, Tclass._module.List()));
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "ListLength (well-formedness)"} CheckWellformed$$_module.__default.ListLength(l#0: DatatypeType)
{
  var $_ReadsFrame: [ref,Field]bool;
  var _mcc#0#0: int;
  var _mcc#1#0: DatatypeType;
  var t#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##l#0: DatatypeType;


    assume {:captureState "Test/test.dfy(6,9): initial state"} true;
    $_ReadsFrame := (lambda $o: ref, $f: Field :: $o != null && $Alloc[$o] ==> false);
    // Check well-formedness of preconditions, and then assume them
    // Check well-formedness of the reads clause
    // Check well-formedness of the decreases clause
    // Check body and ensures clauses
    if (*)
    {
        // Check well-formedness of postcondition and assume false
        assume LitInt(0) <= _module.__default.ListLength($LS($LZ), l#0);
        assume false;
    }
    else
    {
        // Check well-formedness of body and result subset type constraint
        if (l#0 == #_module.List.Nil())
        {
            assume true;
            assert {:id "id7"} $Is(LitInt(0), Tclass._System.nat());
            assume {:id "id8"} _module.__default.ListLength($LS($LZ), l#0) == LitInt(0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.ListLength($LS($LZ), l#0), Tclass._System.nat());
            return;
        }
        else if (l#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#1#0, Tclass._module.List());
            havoc t#Z#0;
            assume true;
            assume {:id "id2"} let#0#0#0 == _mcc#1#0;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List());
            assume {:id "id3"} t#Z#0 == let#0#0#0;
            ##l#0 := t#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#0, Tclass._module.List(), $Heap);
            assume true;
            assert {:id "id4"} DtRank(##l#0) < DtRank(l#0);
            assume _module.__default.ListLength#canCall(t#Z#0);
            assume _module.__default.ListLength#canCall(t#Z#0);
            assert {:id "id5"} $Is(1 + _module.__default.ListLength($LS($LZ), t#Z#0), Tclass._System.nat());
            assume {:id "id6"} _module.__default.ListLength($LS($LZ), l#0)
               == 1 + _module.__default.ListLength($LS($LZ), t#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.ListLength($LS($LZ), l#0), Tclass._System.nat());
            return;
        }
        else
        {
            assume false;
        }

        assume false;
    }
}



// function declaration for _module._default.ListHead
function _module.__default.ListHead(l#0: DatatypeType) : int;

function _module.__default.ListHead#canCall(l#0: DatatypeType) : bool;

function _module.__default.ListHead#requires(DatatypeType) : bool;

// #requires axiom for _module.__default.ListHead
axiom (forall l#0: DatatypeType :: 
  { _module.__default.ListHead#requires(l#0) } 
  $Is(l#0, Tclass._module.List())
     ==> _module.__default.ListHead#requires(l#0)
       == !_module.List#Equal(l#0, #_module.List.Nil()));

// #requires ==> #canCall for _module.__default.ListHead
axiom (forall l#0: DatatypeType :: 
  { _module.__default.ListHead#requires(l#0) } 
  _module.__default.ListHead#requires(l#0)
     ==> _module.__default.ListHead#canCall(l#0));

// definition axiom for _module.__default.ListHead (revealed)
axiom {:id "id9"} (forall l#0: DatatypeType :: 
  { _module.__default.ListHead(l#0) } 
  _module.__default.ListHead#canCall(l#0)
     ==> _module.__default.ListHead(l#0) == _module.List.head(l#0));

// definition axiom for _module.__default.ListHead for all literals (revealed)
axiom {:id "id10"} (forall l#0: DatatypeType :: 
  {:weight 3} { _module.__default.ListHead(Lit(l#0)) } 
  _module.__default.ListHead#canCall(Lit(l#0))
     ==> _module.__default.ListHead(Lit(l#0)) == LitInt(_module.List.head(Lit(l#0))));

procedure {:verboseName "ListHead (well-formedness)"} CheckWellformed$$_module.__default.ListHead(l#0: DatatypeType where $Is(l#0, Tclass._module.List()));
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "ListHead (well-formedness)"} CheckWellformed$$_module.__default.ListHead(l#0: DatatypeType)
{
  var $_ReadsFrame: [ref,Field]bool;


    assume {:captureState "Test/test.dfy(13,9): initial state"} true;
    $_ReadsFrame := (lambda $o: ref, $f: Field :: $o != null && $Alloc[$o] ==> false);
    // Check well-formedness of preconditions, and then assume them
    assume {:id "id11"} !_module.List#Equal(l#0, #_module.List.Nil());
    // Check well-formedness of the reads clause
    // Check well-formedness of the decreases clause
    // Check body and ensures clauses
    if (*)
    {
        // Check well-formedness of postcondition and assume false
        assume false;
    }
    else
    {
        // Check well-formedness of body and result subset type constraint
        assert {:id "id12"} _module.List.Cons_q(l#0);
        assume true;
        assume true;
        assume {:id "id13"} _module.__default.ListHead(l#0) == _module.List.head(l#0);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.ListHead(l#0), TInt);
        return;

        assume false;
    }
}



procedure {:verboseName "LengthPositive (well-formedness)"} CheckWellFormed$$_module.__default.LengthPositive(l#0: DatatypeType
       where $Is(l#0, Tclass._module.List())
         && $IsAlloc(l#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(l#0));
  modifies $Heap, $Alloc;



procedure {:verboseName "LengthPositive (call)"} Call$$_module.__default.LengthPositive(l#0: DatatypeType
       where $Is(l#0, Tclass._module.List())
         && $IsAlloc(l#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(l#0));
  // user-defined preconditions
  free requires {:always_assume} $IsA#_module.List(l#0);
  requires {:id "id16"} !_module.List#Equal(l#0, #_module.List.Nil());
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} _module.__default.ListLength#canCall(l#0);
  ensures {:id "id17"} _module.__default.ListLength($LS($LS($LZ)), l#0) >= LitInt(1);



procedure {:verboseName "LengthPositive (correctness)"} Impl$$_module.__default.LengthPositive(l#0: DatatypeType
       where $Is(l#0, Tclass._module.List())
         && $IsAlloc(l#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(l#0))
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} $IsA#_module.List(l#0);
  requires {:id "id18"} !_module.List#Equal(l#0, #_module.List.Nil());
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} _module.__default.ListLength#canCall(l#0);
  ensures {:id "id19"} _module.__default.ListLength($LS($LS($LZ)), l#0) >= LitInt(1);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "LengthPositive (correctness)"} Impl$$_module.__default.LengthPositive(l#0: DatatypeType) returns ($_reverifyPost: bool)
{
    // AddMethodImpl: LengthPositive, Impl$$_module.__default.LengthPositive
    assume {:captureState "Test/test.dfy(23,0): initial state"} true;
    $_reverifyPost := false;
}



procedure {:verboseName "SumArray (well-formedness)"} CheckWellFormed$$_module.__default.SumArray(a#0: ref
       where $Is(a#0, Tclass._System.array(TInt)) && (a#0 == null || $Alloc[a#0]))
   returns (s#0: int);
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "SumArray (well-formedness)"} CheckWellFormed$$_module.__default.SumArray(a#0: ref) returns (s#0: int)
{

    // AddMethodImpl: SumArray, CheckWellFormed$$_module.__default.SumArray
    assume {:captureState "Test/test.dfy(60,7): initial state"} true;
    assert {:id "id20"} a#0 != null;
    assume true;
    assume {:id "id21"} _System.array.Length(a#0) >= LitInt(1);
    havoc $Heap;
    havoc s#0;
    assume {:captureState "Test/test.dfy(62,17): post-state"} true;
    if (*)
    {
        assume {:id "id22"} s#0 >= LitInt(0);
    }
    else
    {
        assume true;
        assume {:id "id23"} LitInt(0) > s#0;
        assume {:id "id24"} s#0 < 0;
    }
}



procedure {:verboseName "SumArray (call)"} Call$$_module.__default.SumArray(a#0: ref
       where $Is(a#0, Tclass._System.array(TInt)) && (a#0 == null || $Alloc[a#0]))
   returns (s#0: int);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id25"} _System.array.Length(a#0) >= LitInt(1);
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id26"} s#0 >= LitInt(0) || s#0 < 0;



procedure {:verboseName "SumArray (correctness)"} Impl$$_module.__default.SumArray(a#0: ref
       where $Is(a#0, Tclass._System.array(TInt)) && (a#0 == null || $Alloc[a#0]))
   returns (defass#s#0: bool, s#0: int, $_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id27"} _System.array.Length(a#0) >= LitInt(1);
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id28"} s#0 >= LitInt(0) || s#0 < 0;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "SumArray (correctness)"} Impl$$_module.__default.SumArray(a#0: ref) returns (defass#s#0: bool, s#0: int, $_reverifyPost: bool)
{
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $PreLoopAlloc$loop#0: [ref]bool;
  var preLoop$loop#0$defass#s#0: bool;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;

    // AddMethodImpl: SumArray, Impl$$_module.__default.SumArray
    assume {:captureState "Test/test.dfy(63,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(64,5)
    assume true;
    assume true;
    s#0 := LitInt(0);
    defass#s#0 := true;
    assume {:captureState "Test/test.dfy(64,8)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(65,9)
    assume true;
    assume true;
    i#0 := LitInt(0);
    assume {:captureState "Test/test.dfy(65,12)"} true;
    // ----- while statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(66,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $PreLoopAlloc$loop#0 := $Alloc;
    preLoop$loop#0$defass#s#0 := defass#s#0;
    $decr_init$loop#00 := _System.array.Length(a#0) - i#0;
    havoc $w$loop#0;
    assume true;
    assume true;
    assume $w$loop#0 ==> true;
    while (true)
      free invariant true;
      invariant {:id "id33"} $w$loop#0 ==> LitInt(0) <= i#0;
      invariant {:id "id34"} $w$loop#0 ==> i#0 <= _System.array.Length(a#0);
      free invariant true;
      invariant {:id "id36"} $w$loop#0 ==> i#0 >= LitInt(0);
      free invariant preLoop$loop#0$defass#s#0 ==> defass#s#0;
      free invariant _System.array.Length(a#0) - i#0 <= $decr_init$loop#00;
    {
        assume {:captureState "Test/test.dfy(66,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (LitInt(0) <= i#0)
            {
                assert {:id "id31"} {:subsumption 0} a#0 != null;
                assume true;
            }

            assume true;
            assume {:id "id32"} LitInt(0) <= i#0 && i#0 <= _System.array.Length(a#0);
            assume true;
            assume {:id "id35"} i#0 >= LitInt(0);
            assert {:id "id37"} a#0 != null;
            assume true;
            assume true;
            assume false;
        }

        assert {:id "id38"} a#0 != null;
        assume true;
        assume true;
        if (_System.array.Length(a#0) <= i#0)
        {
            break;
        }

        assume true;
        $decr$loop#00 := _System.array.Length(a#0) - i#0;
        // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(70,7)
        assume true;
        assert {:id "id39"} defass#s#0;
        assert {:id "id40"} a#0 != null;
        assert {:id "id41"} 0 <= i#0 && i#0 < _System.array.Length(a#0);
        assume true;
        s#0 := s#0 + $Unbox(read($Heap, a#0, IndexField(i#0))): int;
        defass#s#0 := true;
        assume {:captureState "Test/test.dfy(70,17)"} true;
        // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(71,7)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "Test/test.dfy(71,14)"} true;
        assume true;
        // ----- loop termination check ----- /Users/saline/development/projects/dafny/Test/test.dfy(66,3)
        assert {:id "id44"} 0 <= $decr$loop#00 || _System.array.Length(a#0) - i#0 == $decr$loop#00;
        assert {:id "id45"} _System.array.Length(a#0) - i#0 < $decr$loop#00;
        assume true;
    }

    assert {:id "id46"} defass#s#0;
}



procedure {:verboseName "ProcessList (well-formedness)"} CheckWellFormed$$_module.__default.ProcessList(l#0: DatatypeType
       where $Is(l#0, Tclass._module.List())
         && $IsAlloc(l#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(l#0))
   returns (n#0: int);
  modifies $Heap, $Alloc;



procedure {:verboseName "ProcessList (call)"} Call$$_module.__default.ProcessList(l#0: DatatypeType
       where $Is(l#0, Tclass._module.List())
         && $IsAlloc(l#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(l#0))
   returns (n#0: int);
  // user-defined preconditions
  free requires {:always_assume} $IsA#_module.List(l#0);
  requires {:id "id49"} !_module.List#Equal(l#0, #_module.List.Nil());
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id50"} n#0 >= LitInt(1);



procedure {:verboseName "ProcessList (correctness)"} Impl$$_module.__default.ProcessList(l#0: DatatypeType
       where $Is(l#0, Tclass._module.List())
         && $IsAlloc(l#0, Tclass._module.List(), $Heap)
         && $IsA#_module.List(l#0))
   returns (defass#n#0: bool, n#0: int, $_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} $IsA#_module.List(l#0);
  requires {:id "id51"} !_module.List#Equal(l#0, #_module.List.Nil());
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id52"} n#0 >= LitInt(1);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "ProcessList (correctness)"} Impl$$_module.__default.ProcessList(l#0: DatatypeType) returns (defass#n#0: bool, n#0: int, $_reverifyPost: bool)
{
  var len#0: int where LitInt(0) <= len#0;
  var ##l#0: DatatypeType;
  var l##0: DatatypeType;
  var $PreCallHeap#0: Heap;
  var $PreCallAlloc#0: [ref]bool;
  var cur#0: DatatypeType
     where $Is(cur#0, Tclass._module.List())
       && $IsAlloc(cur#0, Tclass._module.List(), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $PreLoopAlloc$loop#0: [ref]bool;
  var preLoop$loop#0$defass#n#0: bool;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var ##l#1: DatatypeType;
  var ##l#2: DatatypeType;
  var ##l#3: DatatypeType;
  var $decr$loop#00: int;
  var _mcc#0#0_0_0: int;
  var _mcc#1#0_0_0: DatatypeType;
  var t#0_0_0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;

    // AddMethodImpl: ProcessList, Impl$$_module.__default.ProcessList
    assume {:captureState "Test/test.dfy(79,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(80,17)
    assume true;
    ##l#0 := l#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##l#0, Tclass._module.List(), $Heap);
    assume _module.__default.ListLength#canCall(l#0);
    assume _module.__default.ListLength#canCall(l#0);
    len#0 := _module.__default.ListLength($LS($LZ), l#0);
    assume {:captureState "Test/test.dfy(80,32)"} true;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(81,17)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    l##0 := l#0;
    $PreCallHeap#0 := $Heap;
    $PreCallAlloc#0 := $Alloc;
    call {:id "id54"} Call$$_module.__default.LengthPositive(l##0);
    // qf-call-frame LengthPositive: supports=0 reads=0 modified=0
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/test.dfy(81,19)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(82,5)
    assume true;
    assume true;
    n#0 := LitInt(0);
    defass#n#0 := true;
    assume {:captureState "Test/test.dfy(82,8)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(83,11)
    assume true;
    assume true;
    cur#0 := l#0;
    assume {:captureState "Test/test.dfy(83,14)"} true;
    // ----- while statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(84,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $PreLoopAlloc$loop#0 := $Alloc;
    preLoop$loop#0$defass#n#0 := defass#n#0;
    $decr_init$loop#00 := _module.__default.ListLength($LS($LZ), cur#0);
    havoc $w$loop#0;
    assume true;
    assume $w$loop#0
       ==> _module.__default.ListLength#canCall(cur#0)
         && _module.__default.ListLength#canCall(l#0);
    assume $w$loop#0 ==> _module.__default.ListLength#canCall(cur#0);
    while (true)
      free invariant true;
      invariant {:id "id59"} $w$loop#0 ==> n#0 >= LitInt(0);
      free invariant $w$loop#0
         ==> _module.__default.ListLength#canCall(cur#0)
           && _module.__default.ListLength#canCall(l#0);
      invariant {:id "id62"} $w$loop#0
         ==> n#0 + _module.__default.ListLength($LS($LS($LZ)), cur#0)
           == _module.__default.ListLength($LS($LS($LZ)), l#0);
      free invariant preLoop$loop#0$defass#n#0 ==> defass#n#0;
      free invariant _module.__default.ListLength($LS($LZ), cur#0) <= $decr_init$loop#00;
    {
        assume {:captureState "Test/test.dfy(84,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assert {:id "id57"} defass#n#0;
            assume true;
            assume {:id "id58"} n#0 >= LitInt(0);
            assert {:id "id60"} defass#n#0;
            ##l#1 := cur#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#1, Tclass._module.List(), $Heap);
            assume _module.__default.ListLength#canCall(cur#0);
            ##l#2 := l#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#2, Tclass._module.List(), $Heap);
            assume _module.__default.ListLength#canCall(l#0);
            assume _module.__default.ListLength#canCall(cur#0)
               && _module.__default.ListLength#canCall(l#0);
            assume {:id "id61"} n#0 + _module.__default.ListLength($LS($LZ), cur#0)
               == _module.__default.ListLength($LS($LZ), l#0);
            ##l#3 := cur#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#3, Tclass._module.List(), $Heap);
            assume _module.__default.ListLength#canCall(cur#0);
            assume _module.__default.ListLength#canCall(cur#0);
            assume false;
        }

        assume $IsA#_module.List(cur#0);
        if (_module.List#Equal(cur#0, #_module.List.Nil()))
        {
            break;
        }

        assume $w$loop#0 ==> _module.__default.ListLength#canCall(cur#0);
        $decr$loop#00 := _module.__default.ListLength($LS($LZ), cur#0);
        // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(89,7)
        assume true;
        assert {:id "id63"} defass#n#0;
        assume true;
        n#0 := n#0 + 1;
        defass#n#0 := true;
        assume {:captureState "Test/test.dfy(89,14)"} true;
        assume true;
        havoc _mcc#0#0_0_0, _mcc#1#0_0_0;
        if (cur#0 == #_module.List.Nil())
        {
        }
        else if (cur#0 == #_module.List.Cons(_mcc#0#0_0_0, _mcc#1#0_0_0))
        {
            assume $Is(_mcc#1#0_0_0, Tclass._module.List())
               && $IsAlloc(_mcc#1#0_0_0, Tclass._module.List(), $Heap);
            havoc t#0_0_0;
            assume $Is(t#0_0_0, Tclass._module.List())
               && $IsAlloc(t#0_0_0, Tclass._module.List(), $Heap);
            assume {:id "id65"} let#0_0_0#0#0 == _mcc#1#0_0_0;
            assume true;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, Tclass._module.List());
            assume {:id "id66"} t#0_0_0 == let#0_0_0#0#0;
            // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(92,30)
            assume true;
            assume true;
            cur#0 := t#0_0_0;
            assume {:captureState "Test/test.dfy(92,33)"} true;
        }
        else
        {
            assume false;
        }

        assume $w$loop#0 ==> _module.__default.ListLength#canCall(cur#0);
        // ----- loop termination check ----- /Users/saline/development/projects/dafny/Test/test.dfy(84,3)
        assert {:id "id68"} 0 <= $decr$loop#00
           || _module.__default.ListLength($LS($LZ), cur#0) == $decr$loop#00;
        assert {:id "id69"} _module.__default.ListLength($LS($LZ), cur#0) < $decr$loop#00;
        assume n#0 >= LitInt(0)
           ==> _module.__default.ListLength#canCall(cur#0)
             && _module.__default.ListLength#canCall(l#0);
    }

    assert {:id "id70"} defass#n#0;
}



function Tclass._module.Counter() : Ty
uses {
// Tclass._module.Counter Tag
axiom Tag(Tclass._module.Counter()) == Tagclass._module.Counter
   && TagFamily(Tclass._module.Counter()) == tytagFamily$Counter;
}

const unique Tagclass._module.Counter: TyTag;

// Box/unbox axiom for Tclass._module.Counter
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Counter()) } 
  $IsBox(bx, Tclass._module.Counter())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Counter()));

procedure {:verboseName "FillAndCount (well-formedness)"} CheckWellFormed$$_module.__default.FillAndCount(c#0: ref
       where $Is(c#0, Tclass._module.Counter()) && (c#0 == null || $Alloc[c#0]), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt)) && (a#0 == null || $Alloc[a#0]))
   returns (total#0: int);
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "FillAndCount (well-formedness)"} CheckWellFormed$$_module.__default.FillAndCount(c#0: ref, a#0: ref) returns (total#0: int)
{

    // AddMethodImpl: FillAndCount, CheckWellFormed$$_module.__default.FillAndCount
    assume {:captureState "Test/test.dfy(98,7): initial state"} true;
    assert {:id "id71"} c#0 != null;
    assume true;
    assume {:id "id72"} $Unbox(read($Heap, c#0, _module.Counter.value)): int >= LitInt(0);
    assert {:id "id73"} c#0 != null;
    assume true;
    assume {:id "id74"} $Unbox(read($Heap, c#0, _module.Counter.limit)): int >= LitInt(0);
    assert {:id "id75"} a#0 != null;
    assume true;
    assume {:id "id76"} _System.array.Length(a#0) >= LitInt(1);
    havoc $Heap;
    havoc total#0;
    assume {:captureState "Test/test.dfy(102,16): post-state"} true;
    assume {:id "id77"} total#0 >= LitInt(0);
}



procedure {:verboseName "FillAndCount (call)"} Call$$_module.__default.FillAndCount(c#0: ref
       where $Is(c#0, Tclass._module.Counter()) && (c#0 == null || $Alloc[c#0]), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt)) && (a#0 == null || $Alloc[a#0]))
   returns (total#0: int);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id78"} $Unbox(read($Heap, c#0, _module.Counter.value)): int >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id79"} $Unbox(read($Heap, c#0, _module.Counter.limit)): int >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id80"} _System.array.Length(a#0) >= LitInt(1);
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id81"} total#0 >= LitInt(0);



procedure {:verboseName "FillAndCount (correctness)"} Impl$$_module.__default.FillAndCount(c#0: ref
       where $Is(c#0, Tclass._module.Counter()) && (c#0 == null || $Alloc[c#0]), 
    a#0: ref
       where $Is(a#0, Tclass._System.array(TInt)) && (a#0 == null || $Alloc[a#0]))
   returns (defass#total#0: bool, total#0: int, $_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id82"} $Unbox(read($Heap, c#0, _module.Counter.value)): int >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id83"} $Unbox(read($Heap, c#0, _module.Counter.limit)): int >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id84"} _System.array.Length(a#0) >= LitInt(1);
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id85"} total#0 >= LitInt(0);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "FillAndCount (correctness)"} Impl$$_module.__default.FillAndCount(c#0: ref, a#0: ref)
   returns (defass#total#0: bool, total#0: int, $_reverifyPost: bool)
{
  var $PreCallHeap#0: Heap;
  var $PreCallAlloc#0: [ref]bool;
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $PreLoopAlloc$loop#0: [ref]bool;
  var preLoop$loop#0$defass#total#0: bool;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;

    // AddMethodImpl: FillAndCount, Impl$$_module.__default.FillAndCount
    assume {:captureState "Test/test.dfy(104,0): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(105,10)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert {:id "id86"} c#0 != null;
    $PreCallHeap#0 := $Heap;
    $PreCallAlloc#0 := $Alloc;
    assume true;
    call {:id "id87"} Call$$_module.Counter.Reset(c#0);
    // qf-call-frame Reset: supports=2 reads=4 modified=1
    assume c#0 != null && c#0 != c#0
       ==> read($Heap, c#0, _module.Counter.value)
         == read($PreCallHeap#0, c#0, _module.Counter.value);
    assume c#0 != null && c#0 != c#0
       ==> read($Heap, c#0, _module.Counter.limit)
         == read($PreCallHeap#0, c#0, _module.Counter.limit);
    assume a#0 != null && a#0 != c#0
       ==> read($Heap, a#0, _module.Counter.value)
         == read($PreCallHeap#0, a#0, _module.Counter.value);
    assume a#0 != null && a#0 != c#0
       ==> read($Heap, a#0, _module.Counter.limit)
         == read($PreCallHeap#0, a#0, _module.Counter.limit);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/test.dfy(105,11)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(106,9)
    assume true;
    assume true;
    total#0 := LitInt(0);
    defass#total#0 := true;
    assume {:captureState "Test/test.dfy(106,12)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(107,9)
    assume true;
    assume true;
    i#0 := LitInt(0);
    assume {:captureState "Test/test.dfy(107,12)"} true;
    // ----- while statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(108,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $PreLoopAlloc$loop#0 := $Alloc;
    preLoop$loop#0$defass#total#0 := defass#total#0;
    $decr_init$loop#00 := _System.array.Length(a#0) - i#0;
    havoc $w$loop#0;
    assume true;
    assume true;
    assume true;
    assume $w$loop#0 ==> true;
    while (true)
      free invariant true;
      invariant {:id "id92"} $w$loop#0 ==> LitInt(0) <= i#0;
      invariant {:id "id93"} $w$loop#0 ==> i#0 <= _System.array.Length(a#0);
      free invariant true;
      invariant {:id "id96"} $w$loop#0 ==> total#0 >= LitInt(0);
      free invariant true;
      invariant {:id "id99"} $w$loop#0 ==> $Unbox(read($Heap, c#0, _module.Counter.value)): int == LitInt(0);
      free invariant c#0 != null && c#0 != c#0
         ==> read($PreLoopHeap$loop#0, c#0, _module.Counter.value)
           == read($PreLoopHeap$loop#0, c#0, _module.Counter.value);
      free invariant a#0 != null && a#0 != c#0
         ==> read($PreLoopHeap$loop#0, a#0, _module.Counter.value)
           == read($PreLoopHeap$loop#0, a#0, _module.Counter.value);
      free invariant preLoop$loop#0$defass#total#0 ==> defass#total#0;
      free invariant _System.array.Length(a#0) - i#0 <= $decr_init$loop#00;
    {
        assume {:captureState "Test/test.dfy(108,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (LitInt(0) <= i#0)
            {
                assert {:id "id90"} {:subsumption 0} a#0 != null;
                assume true;
            }

            assume true;
            assume {:id "id91"} LitInt(0) <= i#0 && i#0 <= _System.array.Length(a#0);
            assert {:id "id94"} defass#total#0;
            assume true;
            assume {:id "id95"} total#0 >= LitInt(0);
            assert {:id "id97"} {:subsumption 0} c#0 != null;
            assume true;
            assume true;
            assume {:id "id98"} $Unbox(read($Heap, c#0, _module.Counter.value)): int == LitInt(0);
            assert {:id "id100"} a#0 != null;
            assume true;
            assume true;
            assume false;
        }

        assert {:id "id101"} a#0 != null;
        assume true;
        assume true;
        if (_System.array.Length(a#0) <= i#0)
        {
            break;
        }

        assume true;
        $decr$loop#00 := _System.array.Length(a#0) - i#0;
        // ----- if statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(113,5)
        assert {:id "id102"} a#0 != null;
        assert {:id "id103"} 0 <= i#0 && i#0 < _System.array.Length(a#0);
        assume true;
        if ($Unbox(read($Heap, a#0, IndexField(i#0))): int > 0)
        {
            push;
            // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(114,13)
            assume true;
            assert {:id "id104"} defass#total#0;
            assert {:id "id105"} a#0 != null;
            assert {:id "id106"} 0 <= i#0 && i#0 < _System.array.Length(a#0);
            assume true;
            total#0 := total#0 + $Unbox(read($Heap, a#0, IndexField(i#0))): int;
            defass#total#0 := true;
            assume {:captureState "Test/test.dfy(114,27)"} true;
            pop;
        }
        else
        {
        }

        // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(116,7)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "Test/test.dfy(116,14)"} true;
        assume true;
        // ----- loop termination check ----- /Users/saline/development/projects/dafny/Test/test.dfy(108,3)
        assert {:id "id109"} 0 <= $decr$loop#00 || _System.array.Length(a#0) - i#0 == $decr$loop#00;
        assert {:id "id110"} _System.array.Length(a#0) - i#0 < $decr$loop#00;
        assume true;
    }

    assert {:id "id111"} defass#total#0;
}



// Constructor function declaration
function #_module.List.Nil() : DatatypeType
uses {
// Constructor identifier
axiom DatatypeCtorId(#_module.List.Nil()) == ##_module.List.Nil;
// Constructor $Is
axiom $Is(#_module.List.Nil(), Tclass._module.List());
// Constructor literal
axiom #_module.List.Nil() == Lit(#_module.List.Nil());
}

const unique ##_module.List.Nil: DtCtorId
uses {
// Constructor identifier
axiom DatatypeCtorId(#_module.List.Nil()) == ##_module.List.Nil;
}

function _module.List.Nil_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.List.Nil_q(d) } 
  _module.List.Nil_q(d) <==> DatatypeCtorId(d) == ##_module.List.Nil);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.List.Nil_q(d) } 
  _module.List.Nil_q(d) ==> d == #_module.List.Nil());

// Constructor function declaration
function #_module.List.Cons(int, DatatypeType) : DatatypeType;

const unique ##_module.List.Cons: DtCtorId
uses {
// Constructor identifier
axiom (forall a#4#0#0: int, a#4#1#0: DatatypeType :: 
  { #_module.List.Cons(a#4#0#0, a#4#1#0) } 
  DatatypeCtorId(#_module.List.Cons(a#4#0#0, a#4#1#0)) == ##_module.List.Cons);
}

function _module.List.Cons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.List.Cons_q(d) } 
  _module.List.Cons_q(d) <==> DatatypeCtorId(d) == ##_module.List.Cons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.List.Cons_q(d) } 
  _module.List.Cons_q(d)
     ==> (exists a#5#0#0: int, a#5#1#0: DatatypeType :: 
      d == #_module.List.Cons(a#5#0#0, a#5#1#0)));

// Constructor $Is
axiom (forall a#6#0#0: int, a#6#1#0: DatatypeType :: 
  { $Is(#_module.List.Cons(a#6#0#0, a#6#1#0), Tclass._module.List()) } 
  $Is(#_module.List.Cons(a#6#0#0, a#6#1#0), Tclass._module.List())
     <==> $Is(a#6#0#0, TInt) && $Is(a#6#1#0, Tclass._module.List()));

// Constructor literal
axiom (forall a#7#0#0: int, a#7#1#0: DatatypeType :: 
  { #_module.List.Cons(LitInt(a#7#0#0), Lit(a#7#1#0)) } 
  #_module.List.Cons(LitInt(a#7#0#0), Lit(a#7#1#0))
     == Lit(#_module.List.Cons(a#7#0#0, a#7#1#0)));

function _module.List.head(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#8#0#0: int, a#8#1#0: DatatypeType :: 
  { #_module.List.Cons(a#8#0#0, a#8#1#0) } 
  _module.List.head(#_module.List.Cons(a#8#0#0, a#8#1#0)) == a#8#0#0);

function _module.List.tail(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#9#0#0: int, a#9#1#0: DatatypeType :: 
  { #_module.List.Cons(a#9#0#0, a#9#1#0) } 
  _module.List.tail(#_module.List.Cons(a#9#0#0, a#9#1#0)) == a#9#1#0);

// Inductive rank
axiom (forall a#10#0#0: int, a#10#1#0: DatatypeType :: 
  { DtRank(#_module.List.Cons(a#10#0#0, a#10#1#0)) } 
  DtRank(a#10#1#0) < DtRank(#_module.List.Cons(a#10#0#0, a#10#1#0)));

// Depth-one case-split function
function $IsA#_module.List(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.List(d) } 
  $IsA#_module.List(d) ==> _module.List.Nil_q(d) || _module.List.Cons_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.List.Cons_q(d), $Is(d, Tclass._module.List()) } 
    { _module.List.Nil_q(d), $Is(d, Tclass._module.List()) } 
  $Is(d, Tclass._module.List())
     ==> _module.List.Nil_q(d) || _module.List.Cons_q(d));

// Datatype extensional equality declaration
function _module.List#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.List.Nil
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.List#Equal(a, b), _module.List.Nil_q(a) } 
    { _module.List#Equal(a, b), _module.List.Nil_q(b) } 
  _module.List.Nil_q(a) && _module.List.Nil_q(b) ==> _module.List#Equal(a, b));

// Datatype extensional equality definition: #_module.List.Cons
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.List#Equal(a, b), _module.List.Cons_q(a) } 
    { _module.List#Equal(a, b), _module.List.Cons_q(b) } 
  _module.List.Cons_q(a) && _module.List.Cons_q(b)
     ==> (_module.List#Equal(a, b)
       <==> _module.List.head(a) == _module.List.head(b)
         && _module.List#Equal(_module.List.tail(a), _module.List.tail(b))));

// Datatype extensionality axiom: _module.List
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.List#Equal(a, b) } 
  _module.List#Equal(a, b) <==> a == b);

const unique class._module.List: ClassName;

const unique class._module.Counter?: ClassName;

function Tclass._module.Counter?() : Ty
uses {
// Tclass._module.Counter? Tag
axiom Tag(Tclass._module.Counter?()) == Tagclass._module.Counter?
   && TagFamily(Tclass._module.Counter?()) == tytagFamily$Counter;
}

const unique Tagclass._module.Counter?: TyTag;

// Box/unbox axiom for Tclass._module.Counter?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Counter?()) } 
  $IsBox(bx, Tclass._module.Counter?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Counter?()));

// $Is axiom for class Counter
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Counter?()) } 
  $Is($o, Tclass._module.Counter?())
     <==> $o == null || dtype($o) == Tclass._module.Counter?());

const _module.Counter.value: Field
uses {
axiom FDim(_module.Counter.value) == 0
   && FieldOfDecl(class._module.Counter?, field$value) == _module.Counter.value
   && !$IsGhostField(_module.Counter.value);
}

const _module.Counter.limit: Field
uses {
axiom FDim(_module.Counter.limit) == 0
   && FieldOfDecl(class._module.Counter?, field$limit) == _module.Counter.limit
   && !$IsGhostField(_module.Counter.limit);
}

procedure {:verboseName "Counter._ctor (well-formedness)"} CheckWellFormed$$_module.Counter.__ctor(lim#0: int) returns (this: ref);
  modifies $Heap, $Alloc;



procedure {:verboseName "Counter._ctor (call)"} Call$$_module.Counter.__ctor(lim#0: int)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Counter())
         && (this == null || $Alloc[this]));
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id115"} lim#0 >= LitInt(0);
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id116"} $Unbox(read($Heap, this, _module.Counter.value)): int == LitInt(0);
  free ensures {:always_assume} true;
  ensures {:id "id117"} $Unbox(read($Heap, this, _module.Counter.limit)): int == lim#0;
  // constructor allocates the object
  ensures !old($Alloc)[this];



procedure {:verboseName "Counter._ctor (correctness)"} Impl$$_module.Counter.__ctor(lim#0: int) returns (this: ref, $_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id118"} lim#0 >= LitInt(0);
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id119"} $Unbox(read($Heap, this, _module.Counter.value)): int == LitInt(0);
  free ensures {:always_assume} true;
  ensures {:id "id120"} $Unbox(read($Heap, this, _module.Counter.limit)): int == lim#0;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Counter._ctor (correctness)"} Impl$$_module.Counter.__ctor(lim#0: int) returns (this: ref, $_reverifyPost: bool)
{
  var this.value: int;
  var this.limit: int;

    // AddMethodImpl: _ctor, Impl$$_module.Counter.__ctor
    assume {:captureState "Test/test.dfy(36,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/saline/development/projects/dafny/Test/test.dfy(36,3)
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(37,11)
    assume true;
    assume true;
    assume true;
    this.value := LitInt(0);
    assume {:captureState "Test/test.dfy(37,14)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(38,11)
    assume true;
    assume true;
    assume true;
    this.limit := lim#0;
    assume {:captureState "Test/test.dfy(38,16)"} true;
    // ----- new; ----- /Users/saline/development/projects/dafny/Test/test.dfy(36,3)
    assume this != null && $Is(this, Tclass._module.Counter?());
    assume !$Alloc[this];
    assume $Unbox(read($Heap, this, _module.Counter.value)): int == this.value;
    assume $Unbox(read($Heap, this, _module.Counter.limit)): int == this.limit;
    $Alloc := $Alloc[this := true];
    assume true;
    // ----- divided block after new; ----- /Users/saline/development/projects/dafny/Test/test.dfy(36,3)
}



procedure {:verboseName "Counter.Increment (well-formedness)"} CheckWellFormed$$_module.Counter.Increment(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Counter())
         && (this == null || $Alloc[this]));
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Counter.Increment (well-formedness)"} CheckWellFormed$$_module.Counter.Increment(this: ref)
{

    // AddMethodImpl: Increment, CheckWellFormed$$_module.Counter.Increment
    assume {:captureState "Test/test.dfy(41,9): initial state"} true;
    assume true;
    assume true;
    assume {:id "id123"} $Unbox(read($Heap, this, _module.Counter.value)): int
       < $Unbox(read($Heap, this, _module.Counter.limit)): int;
    havoc $Heap;
    assume {:captureState "Test/test.dfy(43,18): post-state"} true;
    assume true;
    assert {:id "id124"} this == null || old($Alloc)[this];
    assume true;
    assume {:id "id125"} $Unbox(read($Heap, this, _module.Counter.value)): int
       == $Unbox(read(old($Heap), this, _module.Counter.value)): int + 1;
    assume true;
    assert {:id "id126"} this == null || old($Alloc)[this];
    assume true;
    assume {:id "id127"} $Unbox(read($Heap, this, _module.Counter.limit)): int
       == $Unbox(read(old($Heap), this, _module.Counter.limit)): int;
}



procedure {:verboseName "Counter.Increment (call)"} Call$$_module.Counter.Increment(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Counter())
         && (this == null || $Alloc[this]));
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id128"} $Unbox(read($Heap, this, _module.Counter.value)): int
     < $Unbox(read($Heap, this, _module.Counter.limit)): int;
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id129"} $Unbox(read($Heap, this, _module.Counter.value)): int
     == $Unbox(read(old($Heap), this, _module.Counter.value)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id130"} $Unbox(read($Heap, this, _module.Counter.limit)): int
     == $Unbox(read(old($Heap), this, _module.Counter.limit)): int;



procedure {:verboseName "Counter.Increment (correctness)"} Impl$$_module.Counter.Increment(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Counter())
         && (this == null || $Alloc[this]))
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id131"} $Unbox(read($Heap, this, _module.Counter.value)): int
     < $Unbox(read($Heap, this, _module.Counter.limit)): int;
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id132"} $Unbox(read($Heap, this, _module.Counter.value)): int
     == $Unbox(read(old($Heap), this, _module.Counter.value)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id133"} $Unbox(read($Heap, this, _module.Counter.limit)): int
     == $Unbox(read(old($Heap), this, _module.Counter.limit)): int;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Counter.Increment (correctness)"} Impl$$_module.Counter.Increment(this: ref) returns ($_reverifyPost: bool)
{
  var $rhs#0: int;

    // AddMethodImpl: Increment, Impl$$_module.Counter.Increment
    assume {:captureState "Test/test.dfy(46,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(47,11)
    assume true;
    assume true;
    assume true;
    assume true;
    $rhs#0 := $Unbox(read($Heap, this, _module.Counter.value)): int + 1;
    $Heap := update($Heap, this, _module.Counter.value, $Box($rhs#0));
    assume true;
    assume {:captureState "Test/test.dfy(47,22)"} true;
}



procedure {:verboseName "Counter.Reset (well-formedness)"} CheckWellFormed$$_module.Counter.Reset(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Counter())
         && (this == null || $Alloc[this]));
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Counter.Reset (well-formedness)"} CheckWellFormed$$_module.Counter.Reset(this: ref)
{

    // AddMethodImpl: Reset, CheckWellFormed$$_module.Counter.Reset
    assume {:captureState "Test/test.dfy(50,9): initial state"} true;
    havoc $Heap;
    assume {:captureState "Test/test.dfy(51,18): post-state"} true;
    assume true;
    assume {:id "id136"} $Unbox(read($Heap, this, _module.Counter.value)): int == LitInt(0);
    assume true;
    assert {:id "id137"} this == null || old($Alloc)[this];
    assume true;
    assume {:id "id138"} $Unbox(read($Heap, this, _module.Counter.limit)): int
       == $Unbox(read(old($Heap), this, _module.Counter.limit)): int;
}



procedure {:verboseName "Counter.Reset (call)"} Call$$_module.Counter.Reset(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Counter())
         && (this == null || $Alloc[this]));
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id139"} $Unbox(read($Heap, this, _module.Counter.value)): int == LitInt(0);
  free ensures {:always_assume} true;
  ensures {:id "id140"} $Unbox(read($Heap, this, _module.Counter.limit)): int
     == $Unbox(read(old($Heap), this, _module.Counter.limit)): int;



procedure {:verboseName "Counter.Reset (correctness)"} Impl$$_module.Counter.Reset(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Counter())
         && (this == null || $Alloc[this]))
   returns ($_reverifyPost: bool);
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id141"} $Unbox(read($Heap, this, _module.Counter.value)): int == LitInt(0);
  free ensures {:always_assume} true;
  ensures {:id "id142"} $Unbox(read($Heap, this, _module.Counter.limit)): int
     == $Unbox(read(old($Heap), this, _module.Counter.limit)): int;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Counter.Reset (correctness)"} Impl$$_module.Counter.Reset(this: ref) returns ($_reverifyPost: bool)
{
  var $rhs#0: int;

    // AddMethodImpl: Reset, Impl$$_module.Counter.Reset
    assume {:captureState "Test/test.dfy(54,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/test.dfy(55,11)
    assume true;
    assume true;
    assume true;
    $rhs#0 := LitInt(0);
    $Heap := update($Heap, this, _module.Counter.value, $Box($rhs#0));
    assume true;
    assume {:captureState "Test/test.dfy(55,14)"} true;
}



// $Is axiom for non-null type _module.Counter
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Counter()) } { $Is(c#0, Tclass._module.Counter?()) } 
  $Is(c#0, Tclass._module.Counter())
     <==> $Is(c#0, Tclass._module.Counter?()) && c#0 != null);

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

const unique tytagFamily$List: TyTagFamily;

const unique tytagFamily$Counter: TyTagFamily;

const unique field$value: NameFamily;

const unique field$limit: NameFamily;
