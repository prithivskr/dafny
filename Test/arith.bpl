
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

revealed function char#ToInt(char) : int;

revealed function char#Plus(char, char) : char;

revealed function char#Minus(char, char) : char;

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
  $IsBox(bx, TInt) ==> $Box($Unbox(bx): int) == bx);

axiom (forall bx: Box :: 
  { $IsBox(bx, TReal) } 
  $IsBox(bx, TReal) ==> $Box($Unbox(bx): real) == bx);

axiom (forall bx: Box :: 
  { $IsBox(bx, TBool) } 
  $IsBox(bx, TBool) ==> $Box($Unbox(bx): bool) == bx);

axiom (forall bx: Box :: 
  { $IsBox(bx, TChar) } 
  $IsBox(bx, TChar) ==> $Box($Unbox(bx): char) == bx);

axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(0)) } 
  $IsBox(bx, TBitvector(0)) ==> $Box($Unbox(bx): Bv0) == bx);

axiom (forall<T> v: T, t: Ty :: 
  { $IsBox($Box(v), t) } 
  $IsBox($Box(v), t) <==> $Is(v, t));

revealed function $Is<T>(T, Ty) : bool;

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

revealed function {:inline} _System.array.Length(a: ref) : int
{
  0
}

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

revealed function {:inline true} INTERNAL_add_boogie(x: int, y: int) : int
{
  x + y
}

revealed function {:inline true} INTERNAL_sub_boogie(x: int, y: int) : int
{
  x - y
}

revealed function {:inline true} INTERNAL_mul_boogie(x: int, y: int) : int
{
  x * y
}

revealed function {:inline true} INTERNAL_div_boogie(x: int, y: int) : int
{
  x div y
}

revealed function {:inline true} INTERNAL_mod_boogie(x: int, y: int) : int
{
  x mod y
}

revealed function {:inline true} INTERNAL_lt_boogie(x: int, y: int) : bool
{
  x < y
}

revealed function {:inline true} INTERNAL_le_boogie(x: int, y: int) : bool
{
  x <= y
}

revealed function {:inline true} INTERNAL_gt_boogie(x: int, y: int) : bool
{
  x > y
}

revealed function {:inline true} INTERNAL_ge_boogie(x: int, y: int) : bool
{
  x >= y
}

revealed function {:inline true} Mul(x: int, y: int) : int
{
  x * y
}

revealed function {:inline true} Div(x: int, y: int) : int
{
  x div y
}

revealed function {:inline true} Mod(x: int, y: int) : int
{
  x mod y
}

revealed function {:inline true} Add(x: int, y: int) : int
{
  x + y
}

revealed function {:inline true} Sub(x: int, y: int) : int
{
  x - y
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
  $IsBox(bx, Tclass._System.nat()) ==> $Box($Unbox(bx): int) == bx);

// $Is axiom for subset type _System.nat
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._System.nat()) } 
  $Is(x#0, Tclass._System.nat()) <==> LitInt(0) <= x#0);

const unique class._System.object?: ClassName;

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
  $IsBox(bx, Tclass._System.object()) ==> $Box($Unbox(bx): ref) == bx);

const unique Tagclass._System.object?: TyTag;

// Box/unbox axiom for Tclass._System.object?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.object?()) } 
  $IsBox(bx, Tclass._System.object?()) ==> $Box($Unbox(bx): ref) == bx);

// $Is axiom for non-null type _System.object
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._System.object()) } { $Is(c#0, Tclass._System.object?()) } 
  $Is(c#0, Tclass._System.object())
     <==> $Is(c#0, Tclass._System.object?()) && c#0 != null);

const unique class._System.array?: ClassName;

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
     ==> $Box($Unbox(bx): ref) == bx);

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
     ==> $Box($Unbox(bx): ref) == bx);

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
     ==> $Box($Unbox(bx): HandleType) == bx);

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
     ==> $Box($Unbox(bx): HandleType) == bx);

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
     ==> $Box($Unbox(bx): HandleType) == bx);

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
  $IsBox(bx, Tclass._System.___hFunc0(#$R)) ==> $Box($Unbox(bx): HandleType) == bx);

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
     ==> $Box($Unbox(bx): HandleType) == bx);

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
     ==> $Box($Unbox(bx): HandleType) == bx);

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
     ==> $Box($Unbox(bx): DatatypeType) == bx);

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
  $IsBox(bx, Tclass._System.Tuple0()) ==> $Box($Unbox(bx): DatatypeType) == bx);

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
     ==> $Box($Unbox(bx): HandleType) == bx);

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
     ==> $Box($Unbox(bx): HandleType) == bx);

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
     ==> $Box($Unbox(bx): HandleType) == bx);

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
  $IsBox(bx, Tclass._module.Node()) ==> $Box($Unbox(bx): ref) == bx);

procedure {:verboseName "Bump (well-formedness)"} CheckWellFormed$$_module.__default.Bump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]));
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Bump (well-formedness)"} CheckWellFormed$$_module.__default.Bump(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref)
{

    // AddMethodImpl: Bump, CheckWellFormed$$_module.__default.Bump
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
    assume {:captureState "Test/arith.dfy(20,84): post-state"} true;
    assert {:id "id15"} a#0 != null;
    assume true;
    assert {:id "id16"} a#0 != null;
    assert {:id "id17"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id18"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 1;
    assert {:id "id19"} a#0 != null;
    assume true;
    assert {:id "id20"} a#0 != null;
    assert {:id "id21"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id22"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id23"} a#0 != null;
    assume true;
    assert {:id "id24"} a#0 != null;
    assert {:id "id25"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id26"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id27"} a#0 != null;
    assume true;
    assert {:id "id28"} a#0 != null;
    assert {:id "id29"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id30"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
    assert {:id "id31"} b#0 != null;
    assume true;
    assert {:id "id32"} b#0 != null;
    assert {:id "id33"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id34"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 1;
    assert {:id "id35"} b#0 != null;
    assume true;
    assert {:id "id36"} b#0 != null;
    assert {:id "id37"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id38"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id39"} b#0 != null;
    assume true;
    assert {:id "id40"} b#0 != null;
    assert {:id "id41"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id42"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id43"} b#0 != null;
    assume true;
    assert {:id "id44"} b#0 != null;
    assert {:id "id45"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id46"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
    assert {:id "id47"} c#0 != null;
    assume true;
    assert {:id "id48"} c#0 != null;
    assert {:id "id49"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id50"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 1;
    assert {:id "id51"} c#0 != null;
    assume true;
    assert {:id "id52"} c#0 != null;
    assert {:id "id53"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id54"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id55"} c#0 != null;
    assume true;
    assert {:id "id56"} c#0 != null;
    assert {:id "id57"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id58"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id59"} c#0 != null;
    assume true;
    assert {:id "id60"} c#0 != null;
    assert {:id "id61"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id62"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
    assert {:id "id63"} d#0 != null;
    assume true;
    assert {:id "id64"} d#0 != null;
    assert {:id "id65"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id66"} $Unbox(read($Heap, d#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 1;
    assert {:id "id67"} d#0 != null;
    assume true;
    assert {:id "id68"} d#0 != null;
    assert {:id "id69"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id70"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
    assert {:id "id71"} d#0 != null;
    assume true;
    assert {:id "id72"} d#0 != null;
    assert {:id "id73"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id74"} $Unbox(read($Heap, d#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
    assert {:id "id75"} d#0 != null;
    assume true;
    assert {:id "id76"} d#0 != null;
    assert {:id "id77"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id78"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
    assert {:id "id79"} e#0 != null;
    assume true;
    assert {:id "id80"} e#0 != null;
    assert {:id "id81"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id82"} $Unbox(read($Heap, e#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 1;
    assert {:id "id83"} e#0 != null;
    assume true;
    assert {:id "id84"} e#0 != null;
    assert {:id "id85"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id86"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
    assert {:id "id87"} e#0 != null;
    assume true;
    assert {:id "id88"} e#0 != null;
    assert {:id "id89"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id90"} $Unbox(read($Heap, e#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
    assert {:id "id91"} e#0 != null;
    assume true;
    assert {:id "id92"} e#0 != null;
    assert {:id "id93"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id94"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
    assert {:id "id95"} f#0 != null;
    assume true;
    assert {:id "id96"} f#0 != null;
    assert {:id "id97"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id98"} $Unbox(read($Heap, f#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 1;
    assert {:id "id99"} f#0 != null;
    assume true;
    assert {:id "id100"} f#0 != null;
    assert {:id "id101"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id102"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
    assert {:id "id103"} f#0 != null;
    assume true;
    assert {:id "id104"} f#0 != null;
    assert {:id "id105"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id106"} $Unbox(read($Heap, f#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
    assert {:id "id107"} f#0 != null;
    assume true;
    assert {:id "id108"} f#0 != null;
    assert {:id "id109"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id110"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
}



procedure {:verboseName "Bump (call)"} Call$$_module.__default.Bump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]));
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
  modifies $Heap, $Alloc;
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



procedure {:verboseName "Bump (correctness)"} Impl$$_module.__default.Bump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]))
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
  modifies $Heap, $Alloc;
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



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Bump (correctness)"} Impl$$_module.__default.Bump(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref)
   returns ($_reverifyPost: bool)
{
  var $rhs#0: int;
  var $rhs#1: int;
  var $rhs#2: int;
  var $rhs#3: int;
  var $rhs#4: int;
  var $rhs#5: int;

    // AddMethodImpl: Bump, Impl$$_module.__default.Bump
    assume {:captureState "Test/arith.dfy(26,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(27,9)
    assert {:id "id189"} a#0 != null;
    assume true;
    assume true;
    assert {:id "id190"} a#0 != null;
    assume true;
    assume true;
    $rhs#0 := $Unbox(read($Heap, a#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, a#0, _module.Node.val, $Box($rhs#0));
    assume true;
    assume {:captureState "Test/arith.dfy(27,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(28,9)
    assert {:id "id193"} b#0 != null;
    assume true;
    assume true;
    assert {:id "id194"} b#0 != null;
    assume true;
    assume true;
    $rhs#1 := $Unbox(read($Heap, b#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, b#0, _module.Node.val, $Box($rhs#1));
    assume true;
    assume {:captureState "Test/arith.dfy(28,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(29,9)
    assert {:id "id197"} c#0 != null;
    assume true;
    assume true;
    assert {:id "id198"} c#0 != null;
    assume true;
    assume true;
    $rhs#2 := $Unbox(read($Heap, c#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, c#0, _module.Node.val, $Box($rhs#2));
    assume true;
    assume {:captureState "Test/arith.dfy(29,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(30,9)
    assert {:id "id201"} d#0 != null;
    assume true;
    assume true;
    assert {:id "id202"} d#0 != null;
    assume true;
    assume true;
    $rhs#3 := $Unbox(read($Heap, d#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, d#0, _module.Node.val, $Box($rhs#3));
    assume true;
    assume {:captureState "Test/arith.dfy(30,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(31,9)
    assert {:id "id205"} e#0 != null;
    assume true;
    assume true;
    assert {:id "id206"} e#0 != null;
    assume true;
    assume true;
    $rhs#4 := $Unbox(read($Heap, e#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, e#0, _module.Node.val, $Box($rhs#4));
    assume true;
    assume {:captureState "Test/arith.dfy(31,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(32,9)
    assert {:id "id209"} f#0 != null;
    assume true;
    assume true;
    assert {:id "id210"} f#0 != null;
    assume true;
    assume true;
    $rhs#5 := $Unbox(read($Heap, f#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, f#0, _module.Node.val, $Box($rhs#5));
    assume true;
    assume {:captureState "Test/arith.dfy(32,20)"} true;
}



procedure {:verboseName "DoubleBump (well-formedness)"} CheckWellFormed$$_module.__default.DoubleBump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]));
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "DoubleBump (well-formedness)"} CheckWellFormed$$_module.__default.DoubleBump(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref)
{

    // AddMethodImpl: DoubleBump, CheckWellFormed$$_module.__default.DoubleBump
    assume {:captureState "Test/arith.dfy(36,7): initial state"} true;
    assume {:id "id213"} a#0 != b#0;
    assume {:id "id214"} a#0 != c#0;
    assume {:id "id215"} a#0 != d#0;
    assume {:id "id216"} a#0 != e#0;
    assume {:id "id217"} a#0 != f#0;
    assume {:id "id218"} b#0 != c#0;
    assume {:id "id219"} b#0 != d#0;
    assume {:id "id220"} b#0 != e#0;
    assume {:id "id221"} b#0 != f#0;
    assume {:id "id222"} c#0 != d#0;
    assume {:id "id223"} c#0 != e#0;
    assume {:id "id224"} c#0 != f#0;
    assume {:id "id225"} d#0 != e#0;
    assume {:id "id226"} d#0 != f#0;
    assume {:id "id227"} e#0 != f#0;
    havoc $Heap;
    assume {:captureState "Test/arith.dfy(42,84): post-state"} true;
    assert {:id "id228"} a#0 != null;
    assume true;
    assert {:id "id229"} a#0 != null;
    assert {:id "id230"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id231"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 2;
    assert {:id "id232"} a#0 != null;
    assume true;
    assert {:id "id233"} a#0 != null;
    assert {:id "id234"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id235"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id236"} a#0 != null;
    assume true;
    assert {:id "id237"} a#0 != null;
    assert {:id "id238"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id239"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id240"} a#0 != null;
    assume true;
    assert {:id "id241"} a#0 != null;
    assert {:id "id242"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id243"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
    assert {:id "id244"} b#0 != null;
    assume true;
    assert {:id "id245"} b#0 != null;
    assert {:id "id246"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id247"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 2;
    assert {:id "id248"} b#0 != null;
    assume true;
    assert {:id "id249"} b#0 != null;
    assert {:id "id250"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id251"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id252"} b#0 != null;
    assume true;
    assert {:id "id253"} b#0 != null;
    assert {:id "id254"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id255"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id256"} b#0 != null;
    assume true;
    assert {:id "id257"} b#0 != null;
    assert {:id "id258"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id259"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
    assert {:id "id260"} c#0 != null;
    assume true;
    assert {:id "id261"} c#0 != null;
    assert {:id "id262"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id263"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 2;
    assert {:id "id264"} c#0 != null;
    assume true;
    assert {:id "id265"} c#0 != null;
    assert {:id "id266"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id267"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id268"} c#0 != null;
    assume true;
    assert {:id "id269"} c#0 != null;
    assert {:id "id270"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id271"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id272"} c#0 != null;
    assume true;
    assert {:id "id273"} c#0 != null;
    assert {:id "id274"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id275"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
    assert {:id "id276"} d#0 != null;
    assume true;
    assert {:id "id277"} d#0 != null;
    assert {:id "id278"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id279"} $Unbox(read($Heap, d#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 2;
    assert {:id "id280"} d#0 != null;
    assume true;
    assert {:id "id281"} d#0 != null;
    assert {:id "id282"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id283"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
    assert {:id "id284"} d#0 != null;
    assume true;
    assert {:id "id285"} d#0 != null;
    assert {:id "id286"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id287"} $Unbox(read($Heap, d#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
    assert {:id "id288"} d#0 != null;
    assume true;
    assert {:id "id289"} d#0 != null;
    assert {:id "id290"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id291"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
    assert {:id "id292"} e#0 != null;
    assume true;
    assert {:id "id293"} e#0 != null;
    assert {:id "id294"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id295"} $Unbox(read($Heap, e#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 2;
    assert {:id "id296"} e#0 != null;
    assume true;
    assert {:id "id297"} e#0 != null;
    assert {:id "id298"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id299"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
    assert {:id "id300"} e#0 != null;
    assume true;
    assert {:id "id301"} e#0 != null;
    assert {:id "id302"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id303"} $Unbox(read($Heap, e#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
    assert {:id "id304"} e#0 != null;
    assume true;
    assert {:id "id305"} e#0 != null;
    assert {:id "id306"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id307"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
    assert {:id "id308"} f#0 != null;
    assume true;
    assert {:id "id309"} f#0 != null;
    assert {:id "id310"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id311"} $Unbox(read($Heap, f#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 2;
    assert {:id "id312"} f#0 != null;
    assume true;
    assert {:id "id313"} f#0 != null;
    assert {:id "id314"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id315"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
    assert {:id "id316"} f#0 != null;
    assume true;
    assert {:id "id317"} f#0 != null;
    assert {:id "id318"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id319"} $Unbox(read($Heap, f#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
    assert {:id "id320"} f#0 != null;
    assume true;
    assert {:id "id321"} f#0 != null;
    assert {:id "id322"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id323"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
}



procedure {:verboseName "DoubleBump (call)"} Call$$_module.__default.DoubleBump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]));
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id324"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id325"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id326"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id327"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id328"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id329"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id330"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id331"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id332"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id333"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id334"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id335"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id336"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id337"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id338"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id339"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id340"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id341"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id342"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id343"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id344"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id345"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id346"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id347"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id348"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id349"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id350"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id351"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id352"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id353"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id354"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id355"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id356"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id357"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id358"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id359"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id360"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id361"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id362"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;



procedure {:verboseName "DoubleBump (correctness)"} Impl$$_module.__default.DoubleBump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]))
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id363"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id364"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id365"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id366"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id367"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id368"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id369"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id370"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id371"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id372"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id373"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id374"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id375"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id376"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id377"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id378"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id379"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id380"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id381"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id382"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id383"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id384"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id385"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id386"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id387"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id388"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id389"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id390"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id391"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id392"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id393"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id394"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id395"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id396"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id397"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id398"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id399"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id400"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id401"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "DoubleBump (correctness)"} Impl$$_module.__default.DoubleBump(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref)
   returns ($_reverifyPost: bool)
{
  var a##0: ref;
  var b##0: ref;
  var c##0: ref;
  var d##0: ref;
  var e##0: ref;
  var f##0: ref;
  var $PreCallHeap#0: Heap;
  var $PreCallAlloc#0: [ref]bool;
  var a##1: ref;
  var b##1: ref;
  var c##1: ref;
  var d##1: ref;
  var e##1: ref;
  var f##1: ref;
  var $PreCallHeap#1: Heap;
  var $PreCallAlloc#1: [ref]bool;

    // AddMethodImpl: DoubleBump, Impl$$_module.__default.DoubleBump
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
    $PreCallHeap#0 := $Heap;
    $PreCallAlloc#0 := $Alloc;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id402"} a##0 == a#0
       || a##0 == b#0
       || a##0 == c#0
       || a##0 == d#0
       || a##0 == e#0
       || a##0 == f#0
       || !old($Alloc)[a##0];
    assert {:id "id403"} b##0 == a#0
       || b##0 == b#0
       || b##0 == c#0
       || b##0 == d#0
       || b##0 == e#0
       || b##0 == f#0
       || !old($Alloc)[b##0];
    assert {:id "id404"} c##0 == a#0
       || c##0 == b#0
       || c##0 == c#0
       || c##0 == d#0
       || c##0 == e#0
       || c##0 == f#0
       || !old($Alloc)[c##0];
    assert {:id "id405"} d##0 == a#0
       || d##0 == b#0
       || d##0 == c#0
       || d##0 == d#0
       || d##0 == e#0
       || d##0 == f#0
       || !old($Alloc)[d##0];
    assert {:id "id406"} e##0 == a#0
       || e##0 == b#0
       || e##0 == c#0
       || e##0 == d#0
       || e##0 == e#0
       || e##0 == f#0
       || !old($Alloc)[e##0];
    assert {:id "id407"} f##0 == a#0
       || f##0 == b#0
       || f##0 == c#0
       || f##0 == d#0
       || f##0 == e#0
       || f##0 == f#0
       || !old($Alloc)[f##0];
    call {:id "id408"} Call$$_module.__default.Bump(a##0, b##0, c##0, d##0, e##0, f##0);
    // qf-call-frame Bump: supports=12 reads=48 modified=6
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.val)
         == read($PreCallHeap#0, a#0, _module.Node.val);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.tag)
         == read($PreCallHeap#0, a#0, _module.Node.tag);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.score)
         == read($PreCallHeap#0, a#0, _module.Node.score);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.rank)
         == read($PreCallHeap#0, a#0, _module.Node.rank);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.val)
         == read($PreCallHeap#0, b#0, _module.Node.val);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.tag)
         == read($PreCallHeap#0, b#0, _module.Node.tag);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.score)
         == read($PreCallHeap#0, b#0, _module.Node.score);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.rank)
         == read($PreCallHeap#0, b#0, _module.Node.rank);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.val)
         == read($PreCallHeap#0, c#0, _module.Node.val);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.tag)
         == read($PreCallHeap#0, c#0, _module.Node.tag);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.score)
         == read($PreCallHeap#0, c#0, _module.Node.score);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.rank)
         == read($PreCallHeap#0, c#0, _module.Node.rank);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.val)
         == read($PreCallHeap#0, d#0, _module.Node.val);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.tag)
         == read($PreCallHeap#0, d#0, _module.Node.tag);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.score)
         == read($PreCallHeap#0, d#0, _module.Node.score);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.rank)
         == read($PreCallHeap#0, d#0, _module.Node.rank);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.val)
         == read($PreCallHeap#0, e#0, _module.Node.val);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.tag)
         == read($PreCallHeap#0, e#0, _module.Node.tag);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.score)
         == read($PreCallHeap#0, e#0, _module.Node.score);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.rank)
         == read($PreCallHeap#0, e#0, _module.Node.rank);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.val)
         == read($PreCallHeap#0, f#0, _module.Node.val);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.tag)
         == read($PreCallHeap#0, f#0, _module.Node.tag);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.score)
         == read($PreCallHeap#0, f#0, _module.Node.score);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.rank)
         == read($PreCallHeap#0, f#0, _module.Node.rank);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.val)
         == read($PreCallHeap#0, a##0, _module.Node.val);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.tag)
         == read($PreCallHeap#0, a##0, _module.Node.tag);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.score)
         == read($PreCallHeap#0, a##0, _module.Node.score);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.rank)
         == read($PreCallHeap#0, a##0, _module.Node.rank);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.val)
         == read($PreCallHeap#0, b##0, _module.Node.val);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.tag)
         == read($PreCallHeap#0, b##0, _module.Node.tag);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.score)
         == read($PreCallHeap#0, b##0, _module.Node.score);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.rank)
         == read($PreCallHeap#0, b##0, _module.Node.rank);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.val)
         == read($PreCallHeap#0, c##0, _module.Node.val);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.tag)
         == read($PreCallHeap#0, c##0, _module.Node.tag);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.score)
         == read($PreCallHeap#0, c##0, _module.Node.score);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.rank)
         == read($PreCallHeap#0, c##0, _module.Node.rank);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.val)
         == read($PreCallHeap#0, d##0, _module.Node.val);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.tag)
         == read($PreCallHeap#0, d##0, _module.Node.tag);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.score)
         == read($PreCallHeap#0, d##0, _module.Node.score);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.rank)
         == read($PreCallHeap#0, d##0, _module.Node.rank);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.val)
         == read($PreCallHeap#0, e##0, _module.Node.val);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.tag)
         == read($PreCallHeap#0, e##0, _module.Node.tag);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.score)
         == read($PreCallHeap#0, e##0, _module.Node.score);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.rank)
         == read($PreCallHeap#0, e##0, _module.Node.rank);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.val)
         == read($PreCallHeap#0, f##0, _module.Node.val);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.tag)
         == read($PreCallHeap#0, f##0, _module.Node.tag);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.score)
         == read($PreCallHeap#0, f##0, _module.Node.score);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.rank)
         == read($PreCallHeap#0, f##0, _module.Node.rank);
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
    $PreCallHeap#1 := $Heap;
    $PreCallAlloc#1 := $Alloc;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id409"} a##1 == a#0
       || a##1 == b#0
       || a##1 == c#0
       || a##1 == d#0
       || a##1 == e#0
       || a##1 == f#0
       || !old($Alloc)[a##1];
    assert {:id "id410"} b##1 == a#0
       || b##1 == b#0
       || b##1 == c#0
       || b##1 == d#0
       || b##1 == e#0
       || b##1 == f#0
       || !old($Alloc)[b##1];
    assert {:id "id411"} c##1 == a#0
       || c##1 == b#0
       || c##1 == c#0
       || c##1 == d#0
       || c##1 == e#0
       || c##1 == f#0
       || !old($Alloc)[c##1];
    assert {:id "id412"} d##1 == a#0
       || d##1 == b#0
       || d##1 == c#0
       || d##1 == d#0
       || d##1 == e#0
       || d##1 == f#0
       || !old($Alloc)[d##1];
    assert {:id "id413"} e##1 == a#0
       || e##1 == b#0
       || e##1 == c#0
       || e##1 == d#0
       || e##1 == e#0
       || e##1 == f#0
       || !old($Alloc)[e##1];
    assert {:id "id414"} f##1 == a#0
       || f##1 == b#0
       || f##1 == c#0
       || f##1 == d#0
       || f##1 == e#0
       || f##1 == f#0
       || !old($Alloc)[f##1];
    call {:id "id415"} Call$$_module.__default.Bump(a##1, b##1, c##1, d##1, e##1, f##1);
    // qf-call-frame Bump: supports=18 reads=72 modified=6
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.val)
         == read($PreCallHeap#1, a#0, _module.Node.val);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.tag)
         == read($PreCallHeap#1, a#0, _module.Node.tag);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.score)
         == read($PreCallHeap#1, a#0, _module.Node.score);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.rank)
         == read($PreCallHeap#1, a#0, _module.Node.rank);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.val)
         == read($PreCallHeap#1, b#0, _module.Node.val);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.tag)
         == read($PreCallHeap#1, b#0, _module.Node.tag);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.score)
         == read($PreCallHeap#1, b#0, _module.Node.score);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.rank)
         == read($PreCallHeap#1, b#0, _module.Node.rank);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.val)
         == read($PreCallHeap#1, c#0, _module.Node.val);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.tag)
         == read($PreCallHeap#1, c#0, _module.Node.tag);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.score)
         == read($PreCallHeap#1, c#0, _module.Node.score);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.rank)
         == read($PreCallHeap#1, c#0, _module.Node.rank);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.val)
         == read($PreCallHeap#1, d#0, _module.Node.val);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.tag)
         == read($PreCallHeap#1, d#0, _module.Node.tag);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.score)
         == read($PreCallHeap#1, d#0, _module.Node.score);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.rank)
         == read($PreCallHeap#1, d#0, _module.Node.rank);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.val)
         == read($PreCallHeap#1, e#0, _module.Node.val);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.tag)
         == read($PreCallHeap#1, e#0, _module.Node.tag);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.score)
         == read($PreCallHeap#1, e#0, _module.Node.score);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.rank)
         == read($PreCallHeap#1, e#0, _module.Node.rank);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.val)
         == read($PreCallHeap#1, f#0, _module.Node.val);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.tag)
         == read($PreCallHeap#1, f#0, _module.Node.tag);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.score)
         == read($PreCallHeap#1, f#0, _module.Node.score);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.rank)
         == read($PreCallHeap#1, f#0, _module.Node.rank);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.val)
         == read($PreCallHeap#1, a##0, _module.Node.val);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.tag)
         == read($PreCallHeap#1, a##0, _module.Node.tag);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.score)
         == read($PreCallHeap#1, a##0, _module.Node.score);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.rank)
         == read($PreCallHeap#1, a##0, _module.Node.rank);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.val)
         == read($PreCallHeap#1, b##0, _module.Node.val);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.tag)
         == read($PreCallHeap#1, b##0, _module.Node.tag);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.score)
         == read($PreCallHeap#1, b##0, _module.Node.score);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.rank)
         == read($PreCallHeap#1, b##0, _module.Node.rank);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.val)
         == read($PreCallHeap#1, c##0, _module.Node.val);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.tag)
         == read($PreCallHeap#1, c##0, _module.Node.tag);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.score)
         == read($PreCallHeap#1, c##0, _module.Node.score);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.rank)
         == read($PreCallHeap#1, c##0, _module.Node.rank);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.val)
         == read($PreCallHeap#1, d##0, _module.Node.val);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.tag)
         == read($PreCallHeap#1, d##0, _module.Node.tag);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.score)
         == read($PreCallHeap#1, d##0, _module.Node.score);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.rank)
         == read($PreCallHeap#1, d##0, _module.Node.rank);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.val)
         == read($PreCallHeap#1, e##0, _module.Node.val);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.tag)
         == read($PreCallHeap#1, e##0, _module.Node.tag);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.score)
         == read($PreCallHeap#1, e##0, _module.Node.score);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.rank)
         == read($PreCallHeap#1, e##0, _module.Node.rank);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.val)
         == read($PreCallHeap#1, f##0, _module.Node.val);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.tag)
         == read($PreCallHeap#1, f##0, _module.Node.tag);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.score)
         == read($PreCallHeap#1, f##0, _module.Node.score);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.rank)
         == read($PreCallHeap#1, f##0, _module.Node.rank);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.val)
         == read($PreCallHeap#1, a##1, _module.Node.val);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.tag)
         == read($PreCallHeap#1, a##1, _module.Node.tag);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.score)
         == read($PreCallHeap#1, a##1, _module.Node.score);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.rank)
         == read($PreCallHeap#1, a##1, _module.Node.rank);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.val)
         == read($PreCallHeap#1, b##1, _module.Node.val);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.tag)
         == read($PreCallHeap#1, b##1, _module.Node.tag);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.score)
         == read($PreCallHeap#1, b##1, _module.Node.score);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.rank)
         == read($PreCallHeap#1, b##1, _module.Node.rank);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.val)
         == read($PreCallHeap#1, c##1, _module.Node.val);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.tag)
         == read($PreCallHeap#1, c##1, _module.Node.tag);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.score)
         == read($PreCallHeap#1, c##1, _module.Node.score);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.rank)
         == read($PreCallHeap#1, c##1, _module.Node.rank);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.val)
         == read($PreCallHeap#1, d##1, _module.Node.val);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.tag)
         == read($PreCallHeap#1, d##1, _module.Node.tag);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.score)
         == read($PreCallHeap#1, d##1, _module.Node.score);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.rank)
         == read($PreCallHeap#1, d##1, _module.Node.rank);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.val)
         == read($PreCallHeap#1, e##1, _module.Node.val);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.tag)
         == read($PreCallHeap#1, e##1, _module.Node.tag);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.score)
         == read($PreCallHeap#1, e##1, _module.Node.score);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.rank)
         == read($PreCallHeap#1, e##1, _module.Node.rank);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.val)
         == read($PreCallHeap#1, f##1, _module.Node.val);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.tag)
         == read($PreCallHeap#1, f##1, _module.Node.tag);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.score)
         == read($PreCallHeap#1, f##1, _module.Node.score);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.rank)
         == read($PreCallHeap#1, f##1, _module.Node.rank);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(50,24)"} true;
}



procedure {:verboseName "QuadBump (well-formedness)"} CheckWellFormed$$_module.__default.QuadBump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]));
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "QuadBump (well-formedness)"} CheckWellFormed$$_module.__default.QuadBump(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref)
{

    // AddMethodImpl: QuadBump, CheckWellFormed$$_module.__default.QuadBump
    assume {:captureState "Test/arith.dfy(54,7): initial state"} true;
    assume {:id "id416"} a#0 != b#0;
    assume {:id "id417"} a#0 != c#0;
    assume {:id "id418"} a#0 != d#0;
    assume {:id "id419"} a#0 != e#0;
    assume {:id "id420"} a#0 != f#0;
    assume {:id "id421"} b#0 != c#0;
    assume {:id "id422"} b#0 != d#0;
    assume {:id "id423"} b#0 != e#0;
    assume {:id "id424"} b#0 != f#0;
    assume {:id "id425"} c#0 != d#0;
    assume {:id "id426"} c#0 != e#0;
    assume {:id "id427"} c#0 != f#0;
    assume {:id "id428"} d#0 != e#0;
    assume {:id "id429"} d#0 != f#0;
    assume {:id "id430"} e#0 != f#0;
    havoc $Heap;
    assume {:captureState "Test/arith.dfy(60,84): post-state"} true;
    assert {:id "id431"} a#0 != null;
    assume true;
    assert {:id "id432"} a#0 != null;
    assert {:id "id433"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id434"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 4;
    assert {:id "id435"} a#0 != null;
    assume true;
    assert {:id "id436"} a#0 != null;
    assert {:id "id437"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id438"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id439"} a#0 != null;
    assume true;
    assert {:id "id440"} a#0 != null;
    assert {:id "id441"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id442"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id443"} a#0 != null;
    assume true;
    assert {:id "id444"} a#0 != null;
    assert {:id "id445"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id446"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
    assert {:id "id447"} b#0 != null;
    assume true;
    assert {:id "id448"} b#0 != null;
    assert {:id "id449"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id450"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 4;
    assert {:id "id451"} b#0 != null;
    assume true;
    assert {:id "id452"} b#0 != null;
    assert {:id "id453"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id454"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id455"} b#0 != null;
    assume true;
    assert {:id "id456"} b#0 != null;
    assert {:id "id457"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id458"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id459"} b#0 != null;
    assume true;
    assert {:id "id460"} b#0 != null;
    assert {:id "id461"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id462"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
    assert {:id "id463"} c#0 != null;
    assume true;
    assert {:id "id464"} c#0 != null;
    assert {:id "id465"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id466"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 4;
    assert {:id "id467"} c#0 != null;
    assume true;
    assert {:id "id468"} c#0 != null;
    assert {:id "id469"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id470"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id471"} c#0 != null;
    assume true;
    assert {:id "id472"} c#0 != null;
    assert {:id "id473"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id474"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id475"} c#0 != null;
    assume true;
    assert {:id "id476"} c#0 != null;
    assert {:id "id477"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id478"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
    assert {:id "id479"} d#0 != null;
    assume true;
    assert {:id "id480"} d#0 != null;
    assert {:id "id481"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id482"} $Unbox(read($Heap, d#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 4;
    assert {:id "id483"} d#0 != null;
    assume true;
    assert {:id "id484"} d#0 != null;
    assert {:id "id485"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id486"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
    assert {:id "id487"} d#0 != null;
    assume true;
    assert {:id "id488"} d#0 != null;
    assert {:id "id489"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id490"} $Unbox(read($Heap, d#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
    assert {:id "id491"} d#0 != null;
    assume true;
    assert {:id "id492"} d#0 != null;
    assert {:id "id493"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id494"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
    assert {:id "id495"} e#0 != null;
    assume true;
    assert {:id "id496"} e#0 != null;
    assert {:id "id497"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id498"} $Unbox(read($Heap, e#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 4;
    assert {:id "id499"} e#0 != null;
    assume true;
    assert {:id "id500"} e#0 != null;
    assert {:id "id501"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id502"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
    assert {:id "id503"} e#0 != null;
    assume true;
    assert {:id "id504"} e#0 != null;
    assert {:id "id505"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id506"} $Unbox(read($Heap, e#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
    assert {:id "id507"} e#0 != null;
    assume true;
    assert {:id "id508"} e#0 != null;
    assert {:id "id509"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id510"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
    assert {:id "id511"} f#0 != null;
    assume true;
    assert {:id "id512"} f#0 != null;
    assert {:id "id513"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id514"} $Unbox(read($Heap, f#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 4;
    assert {:id "id515"} f#0 != null;
    assume true;
    assert {:id "id516"} f#0 != null;
    assert {:id "id517"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id518"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
    assert {:id "id519"} f#0 != null;
    assume true;
    assert {:id "id520"} f#0 != null;
    assert {:id "id521"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id522"} $Unbox(read($Heap, f#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
    assert {:id "id523"} f#0 != null;
    assume true;
    assert {:id "id524"} f#0 != null;
    assert {:id "id525"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id526"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
}



procedure {:verboseName "QuadBump (call)"} Call$$_module.__default.QuadBump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]));
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id527"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id528"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id529"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id530"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id531"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id532"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id533"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id534"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id535"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id536"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id537"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id538"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id539"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id540"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id541"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id542"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id543"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id544"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id545"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id546"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id547"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id548"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id549"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id550"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id551"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id552"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id553"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id554"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id555"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id556"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id557"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id558"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id559"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id560"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id561"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id562"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id563"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id564"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id565"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;



procedure {:verboseName "QuadBump (correctness)"} Impl$$_module.__default.QuadBump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]))
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id566"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id567"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id568"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id569"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id570"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id571"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id572"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id573"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id574"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id575"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id576"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id577"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id578"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id579"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id580"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id581"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id582"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id583"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id584"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id585"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id586"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id587"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id588"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id589"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id590"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id591"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id592"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id593"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id594"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id595"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id596"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id597"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id598"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id599"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id600"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id601"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id602"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id603"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id604"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "QuadBump (correctness)"} Impl$$_module.__default.QuadBump(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref)
   returns ($_reverifyPost: bool)
{
  var a##0: ref;
  var b##0: ref;
  var c##0: ref;
  var d##0: ref;
  var e##0: ref;
  var f##0: ref;
  var $PreCallHeap#0: Heap;
  var $PreCallAlloc#0: [ref]bool;
  var a##1: ref;
  var b##1: ref;
  var c##1: ref;
  var d##1: ref;
  var e##1: ref;
  var f##1: ref;
  var $PreCallHeap#1: Heap;
  var $PreCallAlloc#1: [ref]bool;

    // AddMethodImpl: QuadBump, Impl$$_module.__default.QuadBump
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
    $PreCallHeap#0 := $Heap;
    $PreCallAlloc#0 := $Alloc;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id605"} a##0 == a#0
       || a##0 == b#0
       || a##0 == c#0
       || a##0 == d#0
       || a##0 == e#0
       || a##0 == f#0
       || !old($Alloc)[a##0];
    assert {:id "id606"} b##0 == a#0
       || b##0 == b#0
       || b##0 == c#0
       || b##0 == d#0
       || b##0 == e#0
       || b##0 == f#0
       || !old($Alloc)[b##0];
    assert {:id "id607"} c##0 == a#0
       || c##0 == b#0
       || c##0 == c#0
       || c##0 == d#0
       || c##0 == e#0
       || c##0 == f#0
       || !old($Alloc)[c##0];
    assert {:id "id608"} d##0 == a#0
       || d##0 == b#0
       || d##0 == c#0
       || d##0 == d#0
       || d##0 == e#0
       || d##0 == f#0
       || !old($Alloc)[d##0];
    assert {:id "id609"} e##0 == a#0
       || e##0 == b#0
       || e##0 == c#0
       || e##0 == d#0
       || e##0 == e#0
       || e##0 == f#0
       || !old($Alloc)[e##0];
    assert {:id "id610"} f##0 == a#0
       || f##0 == b#0
       || f##0 == c#0
       || f##0 == d#0
       || f##0 == e#0
       || f##0 == f#0
       || !old($Alloc)[f##0];
    call {:id "id611"} Call$$_module.__default.DoubleBump(a##0, b##0, c##0, d##0, e##0, f##0);
    // qf-call-frame DoubleBump: supports=12 reads=48 modified=6
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.val)
         == read($PreCallHeap#0, a#0, _module.Node.val);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.tag)
         == read($PreCallHeap#0, a#0, _module.Node.tag);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.score)
         == read($PreCallHeap#0, a#0, _module.Node.score);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.rank)
         == read($PreCallHeap#0, a#0, _module.Node.rank);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.val)
         == read($PreCallHeap#0, b#0, _module.Node.val);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.tag)
         == read($PreCallHeap#0, b#0, _module.Node.tag);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.score)
         == read($PreCallHeap#0, b#0, _module.Node.score);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.rank)
         == read($PreCallHeap#0, b#0, _module.Node.rank);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.val)
         == read($PreCallHeap#0, c#0, _module.Node.val);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.tag)
         == read($PreCallHeap#0, c#0, _module.Node.tag);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.score)
         == read($PreCallHeap#0, c#0, _module.Node.score);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.rank)
         == read($PreCallHeap#0, c#0, _module.Node.rank);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.val)
         == read($PreCallHeap#0, d#0, _module.Node.val);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.tag)
         == read($PreCallHeap#0, d#0, _module.Node.tag);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.score)
         == read($PreCallHeap#0, d#0, _module.Node.score);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.rank)
         == read($PreCallHeap#0, d#0, _module.Node.rank);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.val)
         == read($PreCallHeap#0, e#0, _module.Node.val);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.tag)
         == read($PreCallHeap#0, e#0, _module.Node.tag);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.score)
         == read($PreCallHeap#0, e#0, _module.Node.score);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.rank)
         == read($PreCallHeap#0, e#0, _module.Node.rank);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.val)
         == read($PreCallHeap#0, f#0, _module.Node.val);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.tag)
         == read($PreCallHeap#0, f#0, _module.Node.tag);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.score)
         == read($PreCallHeap#0, f#0, _module.Node.score);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.rank)
         == read($PreCallHeap#0, f#0, _module.Node.rank);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.val)
         == read($PreCallHeap#0, a##0, _module.Node.val);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.tag)
         == read($PreCallHeap#0, a##0, _module.Node.tag);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.score)
         == read($PreCallHeap#0, a##0, _module.Node.score);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.rank)
         == read($PreCallHeap#0, a##0, _module.Node.rank);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.val)
         == read($PreCallHeap#0, b##0, _module.Node.val);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.tag)
         == read($PreCallHeap#0, b##0, _module.Node.tag);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.score)
         == read($PreCallHeap#0, b##0, _module.Node.score);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.rank)
         == read($PreCallHeap#0, b##0, _module.Node.rank);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.val)
         == read($PreCallHeap#0, c##0, _module.Node.val);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.tag)
         == read($PreCallHeap#0, c##0, _module.Node.tag);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.score)
         == read($PreCallHeap#0, c##0, _module.Node.score);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.rank)
         == read($PreCallHeap#0, c##0, _module.Node.rank);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.val)
         == read($PreCallHeap#0, d##0, _module.Node.val);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.tag)
         == read($PreCallHeap#0, d##0, _module.Node.tag);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.score)
         == read($PreCallHeap#0, d##0, _module.Node.score);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.rank)
         == read($PreCallHeap#0, d##0, _module.Node.rank);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.val)
         == read($PreCallHeap#0, e##0, _module.Node.val);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.tag)
         == read($PreCallHeap#0, e##0, _module.Node.tag);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.score)
         == read($PreCallHeap#0, e##0, _module.Node.score);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.rank)
         == read($PreCallHeap#0, e##0, _module.Node.rank);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.val)
         == read($PreCallHeap#0, f##0, _module.Node.val);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.tag)
         == read($PreCallHeap#0, f##0, _module.Node.tag);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.score)
         == read($PreCallHeap#0, f##0, _module.Node.score);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.rank)
         == read($PreCallHeap#0, f##0, _module.Node.rank);
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
    $PreCallHeap#1 := $Heap;
    $PreCallAlloc#1 := $Alloc;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id612"} a##1 == a#0
       || a##1 == b#0
       || a##1 == c#0
       || a##1 == d#0
       || a##1 == e#0
       || a##1 == f#0
       || !old($Alloc)[a##1];
    assert {:id "id613"} b##1 == a#0
       || b##1 == b#0
       || b##1 == c#0
       || b##1 == d#0
       || b##1 == e#0
       || b##1 == f#0
       || !old($Alloc)[b##1];
    assert {:id "id614"} c##1 == a#0
       || c##1 == b#0
       || c##1 == c#0
       || c##1 == d#0
       || c##1 == e#0
       || c##1 == f#0
       || !old($Alloc)[c##1];
    assert {:id "id615"} d##1 == a#0
       || d##1 == b#0
       || d##1 == c#0
       || d##1 == d#0
       || d##1 == e#0
       || d##1 == f#0
       || !old($Alloc)[d##1];
    assert {:id "id616"} e##1 == a#0
       || e##1 == b#0
       || e##1 == c#0
       || e##1 == d#0
       || e##1 == e#0
       || e##1 == f#0
       || !old($Alloc)[e##1];
    assert {:id "id617"} f##1 == a#0
       || f##1 == b#0
       || f##1 == c#0
       || f##1 == d#0
       || f##1 == e#0
       || f##1 == f#0
       || !old($Alloc)[f##1];
    call {:id "id618"} Call$$_module.__default.DoubleBump(a##1, b##1, c##1, d##1, e##1, f##1);
    // qf-call-frame DoubleBump: supports=18 reads=72 modified=6
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.val)
         == read($PreCallHeap#1, a#0, _module.Node.val);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.tag)
         == read($PreCallHeap#1, a#0, _module.Node.tag);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.score)
         == read($PreCallHeap#1, a#0, _module.Node.score);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.rank)
         == read($PreCallHeap#1, a#0, _module.Node.rank);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.val)
         == read($PreCallHeap#1, b#0, _module.Node.val);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.tag)
         == read($PreCallHeap#1, b#0, _module.Node.tag);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.score)
         == read($PreCallHeap#1, b#0, _module.Node.score);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.rank)
         == read($PreCallHeap#1, b#0, _module.Node.rank);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.val)
         == read($PreCallHeap#1, c#0, _module.Node.val);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.tag)
         == read($PreCallHeap#1, c#0, _module.Node.tag);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.score)
         == read($PreCallHeap#1, c#0, _module.Node.score);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.rank)
         == read($PreCallHeap#1, c#0, _module.Node.rank);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.val)
         == read($PreCallHeap#1, d#0, _module.Node.val);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.tag)
         == read($PreCallHeap#1, d#0, _module.Node.tag);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.score)
         == read($PreCallHeap#1, d#0, _module.Node.score);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.rank)
         == read($PreCallHeap#1, d#0, _module.Node.rank);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.val)
         == read($PreCallHeap#1, e#0, _module.Node.val);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.tag)
         == read($PreCallHeap#1, e#0, _module.Node.tag);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.score)
         == read($PreCallHeap#1, e#0, _module.Node.score);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.rank)
         == read($PreCallHeap#1, e#0, _module.Node.rank);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.val)
         == read($PreCallHeap#1, f#0, _module.Node.val);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.tag)
         == read($PreCallHeap#1, f#0, _module.Node.tag);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.score)
         == read($PreCallHeap#1, f#0, _module.Node.score);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.rank)
         == read($PreCallHeap#1, f#0, _module.Node.rank);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.val)
         == read($PreCallHeap#1, a##0, _module.Node.val);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.tag)
         == read($PreCallHeap#1, a##0, _module.Node.tag);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.score)
         == read($PreCallHeap#1, a##0, _module.Node.score);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.rank)
         == read($PreCallHeap#1, a##0, _module.Node.rank);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.val)
         == read($PreCallHeap#1, b##0, _module.Node.val);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.tag)
         == read($PreCallHeap#1, b##0, _module.Node.tag);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.score)
         == read($PreCallHeap#1, b##0, _module.Node.score);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.rank)
         == read($PreCallHeap#1, b##0, _module.Node.rank);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.val)
         == read($PreCallHeap#1, c##0, _module.Node.val);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.tag)
         == read($PreCallHeap#1, c##0, _module.Node.tag);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.score)
         == read($PreCallHeap#1, c##0, _module.Node.score);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.rank)
         == read($PreCallHeap#1, c##0, _module.Node.rank);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.val)
         == read($PreCallHeap#1, d##0, _module.Node.val);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.tag)
         == read($PreCallHeap#1, d##0, _module.Node.tag);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.score)
         == read($PreCallHeap#1, d##0, _module.Node.score);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.rank)
         == read($PreCallHeap#1, d##0, _module.Node.rank);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.val)
         == read($PreCallHeap#1, e##0, _module.Node.val);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.tag)
         == read($PreCallHeap#1, e##0, _module.Node.tag);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.score)
         == read($PreCallHeap#1, e##0, _module.Node.score);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.rank)
         == read($PreCallHeap#1, e##0, _module.Node.rank);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.val)
         == read($PreCallHeap#1, f##0, _module.Node.val);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.tag)
         == read($PreCallHeap#1, f##0, _module.Node.tag);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.score)
         == read($PreCallHeap#1, f##0, _module.Node.score);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.rank)
         == read($PreCallHeap#1, f##0, _module.Node.rank);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.val)
         == read($PreCallHeap#1, a##1, _module.Node.val);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.tag)
         == read($PreCallHeap#1, a##1, _module.Node.tag);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.score)
         == read($PreCallHeap#1, a##1, _module.Node.score);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.rank)
         == read($PreCallHeap#1, a##1, _module.Node.rank);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.val)
         == read($PreCallHeap#1, b##1, _module.Node.val);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.tag)
         == read($PreCallHeap#1, b##1, _module.Node.tag);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.score)
         == read($PreCallHeap#1, b##1, _module.Node.score);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.rank)
         == read($PreCallHeap#1, b##1, _module.Node.rank);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.val)
         == read($PreCallHeap#1, c##1, _module.Node.val);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.tag)
         == read($PreCallHeap#1, c##1, _module.Node.tag);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.score)
         == read($PreCallHeap#1, c##1, _module.Node.score);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.rank)
         == read($PreCallHeap#1, c##1, _module.Node.rank);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.val)
         == read($PreCallHeap#1, d##1, _module.Node.val);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.tag)
         == read($PreCallHeap#1, d##1, _module.Node.tag);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.score)
         == read($PreCallHeap#1, d##1, _module.Node.score);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.rank)
         == read($PreCallHeap#1, d##1, _module.Node.rank);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.val)
         == read($PreCallHeap#1, e##1, _module.Node.val);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.tag)
         == read($PreCallHeap#1, e##1, _module.Node.tag);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.score)
         == read($PreCallHeap#1, e##1, _module.Node.score);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.rank)
         == read($PreCallHeap#1, e##1, _module.Node.rank);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.val)
         == read($PreCallHeap#1, f##1, _module.Node.val);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.tag)
         == read($PreCallHeap#1, f##1, _module.Node.tag);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.score)
         == read($PreCallHeap#1, f##1, _module.Node.score);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.rank)
         == read($PreCallHeap#1, f##1, _module.Node.rank);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(68,30)"} true;
}



procedure {:verboseName "OctoBump (well-formedness)"} CheckWellFormed$$_module.__default.OctoBump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]));
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "OctoBump (well-formedness)"} CheckWellFormed$$_module.__default.OctoBump(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref)
{

    // AddMethodImpl: OctoBump, CheckWellFormed$$_module.__default.OctoBump
    assume {:captureState "Test/arith.dfy(72,7): initial state"} true;
    assume {:id "id619"} a#0 != b#0;
    assume {:id "id620"} a#0 != c#0;
    assume {:id "id621"} a#0 != d#0;
    assume {:id "id622"} a#0 != e#0;
    assume {:id "id623"} a#0 != f#0;
    assume {:id "id624"} b#0 != c#0;
    assume {:id "id625"} b#0 != d#0;
    assume {:id "id626"} b#0 != e#0;
    assume {:id "id627"} b#0 != f#0;
    assume {:id "id628"} c#0 != d#0;
    assume {:id "id629"} c#0 != e#0;
    assume {:id "id630"} c#0 != f#0;
    assume {:id "id631"} d#0 != e#0;
    assume {:id "id632"} d#0 != f#0;
    assume {:id "id633"} e#0 != f#0;
    havoc $Heap;
    assume {:captureState "Test/arith.dfy(78,84): post-state"} true;
    assert {:id "id634"} a#0 != null;
    assume true;
    assert {:id "id635"} a#0 != null;
    assert {:id "id636"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id637"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 8;
    assert {:id "id638"} a#0 != null;
    assume true;
    assert {:id "id639"} a#0 != null;
    assert {:id "id640"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id641"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id642"} a#0 != null;
    assume true;
    assert {:id "id643"} a#0 != null;
    assert {:id "id644"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id645"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id646"} a#0 != null;
    assume true;
    assert {:id "id647"} a#0 != null;
    assert {:id "id648"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id649"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
    assert {:id "id650"} b#0 != null;
    assume true;
    assert {:id "id651"} b#0 != null;
    assert {:id "id652"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id653"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 8;
    assert {:id "id654"} b#0 != null;
    assume true;
    assert {:id "id655"} b#0 != null;
    assert {:id "id656"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id657"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id658"} b#0 != null;
    assume true;
    assert {:id "id659"} b#0 != null;
    assert {:id "id660"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id661"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id662"} b#0 != null;
    assume true;
    assert {:id "id663"} b#0 != null;
    assert {:id "id664"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id665"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
    assert {:id "id666"} c#0 != null;
    assume true;
    assert {:id "id667"} c#0 != null;
    assert {:id "id668"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id669"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 8;
    assert {:id "id670"} c#0 != null;
    assume true;
    assert {:id "id671"} c#0 != null;
    assert {:id "id672"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id673"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id674"} c#0 != null;
    assume true;
    assert {:id "id675"} c#0 != null;
    assert {:id "id676"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id677"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id678"} c#0 != null;
    assume true;
    assert {:id "id679"} c#0 != null;
    assert {:id "id680"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id681"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
    assert {:id "id682"} d#0 != null;
    assume true;
    assert {:id "id683"} d#0 != null;
    assert {:id "id684"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id685"} $Unbox(read($Heap, d#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 8;
    assert {:id "id686"} d#0 != null;
    assume true;
    assert {:id "id687"} d#0 != null;
    assert {:id "id688"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id689"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
    assert {:id "id690"} d#0 != null;
    assume true;
    assert {:id "id691"} d#0 != null;
    assert {:id "id692"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id693"} $Unbox(read($Heap, d#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
    assert {:id "id694"} d#0 != null;
    assume true;
    assert {:id "id695"} d#0 != null;
    assert {:id "id696"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id697"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
    assert {:id "id698"} e#0 != null;
    assume true;
    assert {:id "id699"} e#0 != null;
    assert {:id "id700"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id701"} $Unbox(read($Heap, e#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 8;
    assert {:id "id702"} e#0 != null;
    assume true;
    assert {:id "id703"} e#0 != null;
    assert {:id "id704"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id705"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
    assert {:id "id706"} e#0 != null;
    assume true;
    assert {:id "id707"} e#0 != null;
    assert {:id "id708"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id709"} $Unbox(read($Heap, e#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
    assert {:id "id710"} e#0 != null;
    assume true;
    assert {:id "id711"} e#0 != null;
    assert {:id "id712"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id713"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
    assert {:id "id714"} f#0 != null;
    assume true;
    assert {:id "id715"} f#0 != null;
    assert {:id "id716"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id717"} $Unbox(read($Heap, f#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 8;
    assert {:id "id718"} f#0 != null;
    assume true;
    assert {:id "id719"} f#0 != null;
    assert {:id "id720"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id721"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
    assert {:id "id722"} f#0 != null;
    assume true;
    assert {:id "id723"} f#0 != null;
    assert {:id "id724"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id725"} $Unbox(read($Heap, f#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
    assert {:id "id726"} f#0 != null;
    assume true;
    assert {:id "id727"} f#0 != null;
    assert {:id "id728"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id729"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
}



procedure {:verboseName "OctoBump (call)"} Call$$_module.__default.OctoBump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]));
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id730"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id731"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id732"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id733"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id734"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id735"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id736"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id737"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id738"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id739"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id740"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id741"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id742"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id743"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id744"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id745"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id746"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id747"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id748"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id749"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id750"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id751"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id752"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id753"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id754"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id755"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id756"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id757"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id758"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id759"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id760"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id761"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id762"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id763"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id764"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id765"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id766"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id767"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id768"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;



procedure {:verboseName "OctoBump (correctness)"} Impl$$_module.__default.OctoBump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]))
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id769"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id770"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id771"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id772"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id773"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id774"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id775"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id776"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id777"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id778"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id779"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id780"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id781"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id782"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id783"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id784"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id785"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id786"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id787"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id788"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id789"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id790"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id791"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id792"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id793"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id794"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id795"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id796"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id797"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id798"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id799"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id800"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id801"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id802"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id803"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id804"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 8;
  free ensures {:always_assume} true;
  ensures {:id "id805"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id806"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id807"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "OctoBump (correctness)"} Impl$$_module.__default.OctoBump(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref)
   returns ($_reverifyPost: bool)
{
  var a##0: ref;
  var b##0: ref;
  var c##0: ref;
  var d##0: ref;
  var e##0: ref;
  var f##0: ref;
  var $PreCallHeap#0: Heap;
  var $PreCallAlloc#0: [ref]bool;
  var a##1: ref;
  var b##1: ref;
  var c##1: ref;
  var d##1: ref;
  var e##1: ref;
  var f##1: ref;
  var $PreCallHeap#1: Heap;
  var $PreCallAlloc#1: [ref]bool;

    // AddMethodImpl: OctoBump, Impl$$_module.__default.OctoBump
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
    $PreCallHeap#0 := $Heap;
    $PreCallAlloc#0 := $Alloc;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id808"} a##0 == a#0
       || a##0 == b#0
       || a##0 == c#0
       || a##0 == d#0
       || a##0 == e#0
       || a##0 == f#0
       || !old($Alloc)[a##0];
    assert {:id "id809"} b##0 == a#0
       || b##0 == b#0
       || b##0 == c#0
       || b##0 == d#0
       || b##0 == e#0
       || b##0 == f#0
       || !old($Alloc)[b##0];
    assert {:id "id810"} c##0 == a#0
       || c##0 == b#0
       || c##0 == c#0
       || c##0 == d#0
       || c##0 == e#0
       || c##0 == f#0
       || !old($Alloc)[c##0];
    assert {:id "id811"} d##0 == a#0
       || d##0 == b#0
       || d##0 == c#0
       || d##0 == d#0
       || d##0 == e#0
       || d##0 == f#0
       || !old($Alloc)[d##0];
    assert {:id "id812"} e##0 == a#0
       || e##0 == b#0
       || e##0 == c#0
       || e##0 == d#0
       || e##0 == e#0
       || e##0 == f#0
       || !old($Alloc)[e##0];
    assert {:id "id813"} f##0 == a#0
       || f##0 == b#0
       || f##0 == c#0
       || f##0 == d#0
       || f##0 == e#0
       || f##0 == f#0
       || !old($Alloc)[f##0];
    call {:id "id814"} Call$$_module.__default.QuadBump(a##0, b##0, c##0, d##0, e##0, f##0);
    // qf-call-frame QuadBump: supports=12 reads=48 modified=6
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.val)
         == read($PreCallHeap#0, a#0, _module.Node.val);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.tag)
         == read($PreCallHeap#0, a#0, _module.Node.tag);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.score)
         == read($PreCallHeap#0, a#0, _module.Node.score);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.rank)
         == read($PreCallHeap#0, a#0, _module.Node.rank);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.val)
         == read($PreCallHeap#0, b#0, _module.Node.val);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.tag)
         == read($PreCallHeap#0, b#0, _module.Node.tag);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.score)
         == read($PreCallHeap#0, b#0, _module.Node.score);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.rank)
         == read($PreCallHeap#0, b#0, _module.Node.rank);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.val)
         == read($PreCallHeap#0, c#0, _module.Node.val);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.tag)
         == read($PreCallHeap#0, c#0, _module.Node.tag);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.score)
         == read($PreCallHeap#0, c#0, _module.Node.score);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.rank)
         == read($PreCallHeap#0, c#0, _module.Node.rank);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.val)
         == read($PreCallHeap#0, d#0, _module.Node.val);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.tag)
         == read($PreCallHeap#0, d#0, _module.Node.tag);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.score)
         == read($PreCallHeap#0, d#0, _module.Node.score);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.rank)
         == read($PreCallHeap#0, d#0, _module.Node.rank);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.val)
         == read($PreCallHeap#0, e#0, _module.Node.val);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.tag)
         == read($PreCallHeap#0, e#0, _module.Node.tag);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.score)
         == read($PreCallHeap#0, e#0, _module.Node.score);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.rank)
         == read($PreCallHeap#0, e#0, _module.Node.rank);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.val)
         == read($PreCallHeap#0, f#0, _module.Node.val);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.tag)
         == read($PreCallHeap#0, f#0, _module.Node.tag);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.score)
         == read($PreCallHeap#0, f#0, _module.Node.score);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.rank)
         == read($PreCallHeap#0, f#0, _module.Node.rank);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.val)
         == read($PreCallHeap#0, a##0, _module.Node.val);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.tag)
         == read($PreCallHeap#0, a##0, _module.Node.tag);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.score)
         == read($PreCallHeap#0, a##0, _module.Node.score);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.rank)
         == read($PreCallHeap#0, a##0, _module.Node.rank);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.val)
         == read($PreCallHeap#0, b##0, _module.Node.val);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.tag)
         == read($PreCallHeap#0, b##0, _module.Node.tag);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.score)
         == read($PreCallHeap#0, b##0, _module.Node.score);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.rank)
         == read($PreCallHeap#0, b##0, _module.Node.rank);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.val)
         == read($PreCallHeap#0, c##0, _module.Node.val);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.tag)
         == read($PreCallHeap#0, c##0, _module.Node.tag);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.score)
         == read($PreCallHeap#0, c##0, _module.Node.score);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.rank)
         == read($PreCallHeap#0, c##0, _module.Node.rank);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.val)
         == read($PreCallHeap#0, d##0, _module.Node.val);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.tag)
         == read($PreCallHeap#0, d##0, _module.Node.tag);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.score)
         == read($PreCallHeap#0, d##0, _module.Node.score);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.rank)
         == read($PreCallHeap#0, d##0, _module.Node.rank);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.val)
         == read($PreCallHeap#0, e##0, _module.Node.val);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.tag)
         == read($PreCallHeap#0, e##0, _module.Node.tag);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.score)
         == read($PreCallHeap#0, e##0, _module.Node.score);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.rank)
         == read($PreCallHeap#0, e##0, _module.Node.rank);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.val)
         == read($PreCallHeap#0, f##0, _module.Node.val);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.tag)
         == read($PreCallHeap#0, f##0, _module.Node.tag);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.score)
         == read($PreCallHeap#0, f##0, _module.Node.score);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.rank)
         == read($PreCallHeap#0, f##0, _module.Node.rank);
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
    $PreCallHeap#1 := $Heap;
    $PreCallAlloc#1 := $Alloc;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id815"} a##1 == a#0
       || a##1 == b#0
       || a##1 == c#0
       || a##1 == d#0
       || a##1 == e#0
       || a##1 == f#0
       || !old($Alloc)[a##1];
    assert {:id "id816"} b##1 == a#0
       || b##1 == b#0
       || b##1 == c#0
       || b##1 == d#0
       || b##1 == e#0
       || b##1 == f#0
       || !old($Alloc)[b##1];
    assert {:id "id817"} c##1 == a#0
       || c##1 == b#0
       || c##1 == c#0
       || c##1 == d#0
       || c##1 == e#0
       || c##1 == f#0
       || !old($Alloc)[c##1];
    assert {:id "id818"} d##1 == a#0
       || d##1 == b#0
       || d##1 == c#0
       || d##1 == d#0
       || d##1 == e#0
       || d##1 == f#0
       || !old($Alloc)[d##1];
    assert {:id "id819"} e##1 == a#0
       || e##1 == b#0
       || e##1 == c#0
       || e##1 == d#0
       || e##1 == e#0
       || e##1 == f#0
       || !old($Alloc)[e##1];
    assert {:id "id820"} f##1 == a#0
       || f##1 == b#0
       || f##1 == c#0
       || f##1 == d#0
       || f##1 == e#0
       || f##1 == f#0
       || !old($Alloc)[f##1];
    call {:id "id821"} Call$$_module.__default.QuadBump(a##1, b##1, c##1, d##1, e##1, f##1);
    // qf-call-frame QuadBump: supports=18 reads=72 modified=6
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.val)
         == read($PreCallHeap#1, a#0, _module.Node.val);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.tag)
         == read($PreCallHeap#1, a#0, _module.Node.tag);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.score)
         == read($PreCallHeap#1, a#0, _module.Node.score);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.rank)
         == read($PreCallHeap#1, a#0, _module.Node.rank);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.val)
         == read($PreCallHeap#1, b#0, _module.Node.val);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.tag)
         == read($PreCallHeap#1, b#0, _module.Node.tag);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.score)
         == read($PreCallHeap#1, b#0, _module.Node.score);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.rank)
         == read($PreCallHeap#1, b#0, _module.Node.rank);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.val)
         == read($PreCallHeap#1, c#0, _module.Node.val);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.tag)
         == read($PreCallHeap#1, c#0, _module.Node.tag);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.score)
         == read($PreCallHeap#1, c#0, _module.Node.score);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.rank)
         == read($PreCallHeap#1, c#0, _module.Node.rank);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.val)
         == read($PreCallHeap#1, d#0, _module.Node.val);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.tag)
         == read($PreCallHeap#1, d#0, _module.Node.tag);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.score)
         == read($PreCallHeap#1, d#0, _module.Node.score);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.rank)
         == read($PreCallHeap#1, d#0, _module.Node.rank);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.val)
         == read($PreCallHeap#1, e#0, _module.Node.val);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.tag)
         == read($PreCallHeap#1, e#0, _module.Node.tag);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.score)
         == read($PreCallHeap#1, e#0, _module.Node.score);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.rank)
         == read($PreCallHeap#1, e#0, _module.Node.rank);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.val)
         == read($PreCallHeap#1, f#0, _module.Node.val);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.tag)
         == read($PreCallHeap#1, f#0, _module.Node.tag);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.score)
         == read($PreCallHeap#1, f#0, _module.Node.score);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.rank)
         == read($PreCallHeap#1, f#0, _module.Node.rank);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.val)
         == read($PreCallHeap#1, a##0, _module.Node.val);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.tag)
         == read($PreCallHeap#1, a##0, _module.Node.tag);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.score)
         == read($PreCallHeap#1, a##0, _module.Node.score);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.rank)
         == read($PreCallHeap#1, a##0, _module.Node.rank);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.val)
         == read($PreCallHeap#1, b##0, _module.Node.val);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.tag)
         == read($PreCallHeap#1, b##0, _module.Node.tag);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.score)
         == read($PreCallHeap#1, b##0, _module.Node.score);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.rank)
         == read($PreCallHeap#1, b##0, _module.Node.rank);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.val)
         == read($PreCallHeap#1, c##0, _module.Node.val);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.tag)
         == read($PreCallHeap#1, c##0, _module.Node.tag);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.score)
         == read($PreCallHeap#1, c##0, _module.Node.score);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.rank)
         == read($PreCallHeap#1, c##0, _module.Node.rank);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.val)
         == read($PreCallHeap#1, d##0, _module.Node.val);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.tag)
         == read($PreCallHeap#1, d##0, _module.Node.tag);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.score)
         == read($PreCallHeap#1, d##0, _module.Node.score);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.rank)
         == read($PreCallHeap#1, d##0, _module.Node.rank);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.val)
         == read($PreCallHeap#1, e##0, _module.Node.val);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.tag)
         == read($PreCallHeap#1, e##0, _module.Node.tag);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.score)
         == read($PreCallHeap#1, e##0, _module.Node.score);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.rank)
         == read($PreCallHeap#1, e##0, _module.Node.rank);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.val)
         == read($PreCallHeap#1, f##0, _module.Node.val);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.tag)
         == read($PreCallHeap#1, f##0, _module.Node.tag);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.score)
         == read($PreCallHeap#1, f##0, _module.Node.score);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.rank)
         == read($PreCallHeap#1, f##0, _module.Node.rank);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.val)
         == read($PreCallHeap#1, a##1, _module.Node.val);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.tag)
         == read($PreCallHeap#1, a##1, _module.Node.tag);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.score)
         == read($PreCallHeap#1, a##1, _module.Node.score);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.rank)
         == read($PreCallHeap#1, a##1, _module.Node.rank);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.val)
         == read($PreCallHeap#1, b##1, _module.Node.val);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.tag)
         == read($PreCallHeap#1, b##1, _module.Node.tag);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.score)
         == read($PreCallHeap#1, b##1, _module.Node.score);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.rank)
         == read($PreCallHeap#1, b##1, _module.Node.rank);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.val)
         == read($PreCallHeap#1, c##1, _module.Node.val);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.tag)
         == read($PreCallHeap#1, c##1, _module.Node.tag);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.score)
         == read($PreCallHeap#1, c##1, _module.Node.score);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.rank)
         == read($PreCallHeap#1, c##1, _module.Node.rank);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.val)
         == read($PreCallHeap#1, d##1, _module.Node.val);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.tag)
         == read($PreCallHeap#1, d##1, _module.Node.tag);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.score)
         == read($PreCallHeap#1, d##1, _module.Node.score);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.rank)
         == read($PreCallHeap#1, d##1, _module.Node.rank);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.val)
         == read($PreCallHeap#1, e##1, _module.Node.val);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.tag)
         == read($PreCallHeap#1, e##1, _module.Node.tag);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.score)
         == read($PreCallHeap#1, e##1, _module.Node.score);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.rank)
         == read($PreCallHeap#1, e##1, _module.Node.rank);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.val)
         == read($PreCallHeap#1, f##1, _module.Node.val);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.tag)
         == read($PreCallHeap#1, f##1, _module.Node.tag);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.score)
         == read($PreCallHeap#1, f##1, _module.Node.score);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.rank)
         == read($PreCallHeap#1, f##1, _module.Node.rank);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(86,28)"} true;
}



procedure {:verboseName "CrossBump (well-formedness)"} CheckWellFormed$$_module.__default.CrossBump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    p#0: ref where $Is(p#0, Tclass._module.Node()) && (p#0 == null || $Alloc[p#0]), 
    q#0: ref where $Is(q#0, Tclass._module.Node()) && (q#0 == null || $Alloc[q#0]), 
    r#0: ref where $Is(r#0, Tclass._module.Node()) && (r#0 == null || $Alloc[r#0]));
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "CrossBump (well-formedness)"} CheckWellFormed$$_module.__default.CrossBump(a#0: ref, b#0: ref, c#0: ref, p#0: ref, q#0: ref, r#0: ref)
{

    // AddMethodImpl: CrossBump, CheckWellFormed$$_module.__default.CrossBump
    assume {:captureState "Test/arith.dfy(93,7): initial state"} true;
    assume {:id "id822"} a#0 != b#0;
    assume {:id "id823"} a#0 != c#0;
    assume {:id "id824"} b#0 != c#0;
    assume {:id "id825"} p#0 != q#0;
    assume {:id "id826"} p#0 != r#0;
    assume {:id "id827"} q#0 != r#0;
    assume {:id "id828"} a#0 != p#0;
    assume {:id "id829"} a#0 != q#0;
    assume {:id "id830"} a#0 != r#0;
    assume {:id "id831"} b#0 != p#0;
    assume {:id "id832"} b#0 != q#0;
    assume {:id "id833"} b#0 != r#0;
    assume {:id "id834"} c#0 != p#0;
    assume {:id "id835"} c#0 != q#0;
    assume {:id "id836"} c#0 != r#0;
    havoc $Heap;
    assume {:captureState "Test/arith.dfy(100,84): post-state"} true;
    assert {:id "id837"} a#0 != null;
    assume true;
    assert {:id "id838"} a#0 != null;
    assert {:id "id839"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id840"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 1;
    assert {:id "id841"} a#0 != null;
    assume true;
    assert {:id "id842"} a#0 != null;
    assert {:id "id843"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id844"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id845"} a#0 != null;
    assume true;
    assert {:id "id846"} a#0 != null;
    assert {:id "id847"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id848"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id849"} a#0 != null;
    assume true;
    assert {:id "id850"} a#0 != null;
    assert {:id "id851"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id852"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
    assert {:id "id853"} b#0 != null;
    assume true;
    assert {:id "id854"} b#0 != null;
    assert {:id "id855"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id856"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 1;
    assert {:id "id857"} b#0 != null;
    assume true;
    assert {:id "id858"} b#0 != null;
    assert {:id "id859"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id860"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id861"} b#0 != null;
    assume true;
    assert {:id "id862"} b#0 != null;
    assert {:id "id863"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id864"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id865"} b#0 != null;
    assume true;
    assert {:id "id866"} b#0 != null;
    assert {:id "id867"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id868"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
    assert {:id "id869"} c#0 != null;
    assume true;
    assert {:id "id870"} c#0 != null;
    assert {:id "id871"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id872"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 1;
    assert {:id "id873"} c#0 != null;
    assume true;
    assert {:id "id874"} c#0 != null;
    assert {:id "id875"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id876"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id877"} c#0 != null;
    assume true;
    assert {:id "id878"} c#0 != null;
    assert {:id "id879"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id880"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id881"} c#0 != null;
    assume true;
    assert {:id "id882"} c#0 != null;
    assert {:id "id883"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id884"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
    assert {:id "id885"} p#0 != null;
    assume true;
    assert {:id "id886"} p#0 != null;
    assert {:id "id887"} p#0 == null || old($Alloc)[p#0];
    assume true;
    assume {:id "id888"} $Unbox(read($Heap, p#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), p#0, _module.Node.val)): int + 1;
    assert {:id "id889"} p#0 != null;
    assume true;
    assert {:id "id890"} p#0 != null;
    assert {:id "id891"} p#0 == null || old($Alloc)[p#0];
    assume true;
    assume {:id "id892"} $Unbox(read($Heap, p#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), p#0, _module.Node.tag)): int;
    assert {:id "id893"} p#0 != null;
    assume true;
    assert {:id "id894"} p#0 != null;
    assert {:id "id895"} p#0 == null || old($Alloc)[p#0];
    assume true;
    assume {:id "id896"} $Unbox(read($Heap, p#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), p#0, _module.Node.score)): int;
    assert {:id "id897"} p#0 != null;
    assume true;
    assert {:id "id898"} p#0 != null;
    assert {:id "id899"} p#0 == null || old($Alloc)[p#0];
    assume true;
    assume {:id "id900"} $Unbox(read($Heap, p#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), p#0, _module.Node.rank)): int;
    assert {:id "id901"} q#0 != null;
    assume true;
    assert {:id "id902"} q#0 != null;
    assert {:id "id903"} q#0 == null || old($Alloc)[q#0];
    assume true;
    assume {:id "id904"} $Unbox(read($Heap, q#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), q#0, _module.Node.val)): int + 1;
    assert {:id "id905"} q#0 != null;
    assume true;
    assert {:id "id906"} q#0 != null;
    assert {:id "id907"} q#0 == null || old($Alloc)[q#0];
    assume true;
    assume {:id "id908"} $Unbox(read($Heap, q#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), q#0, _module.Node.tag)): int;
    assert {:id "id909"} q#0 != null;
    assume true;
    assert {:id "id910"} q#0 != null;
    assert {:id "id911"} q#0 == null || old($Alloc)[q#0];
    assume true;
    assume {:id "id912"} $Unbox(read($Heap, q#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), q#0, _module.Node.score)): int;
    assert {:id "id913"} q#0 != null;
    assume true;
    assert {:id "id914"} q#0 != null;
    assert {:id "id915"} q#0 == null || old($Alloc)[q#0];
    assume true;
    assume {:id "id916"} $Unbox(read($Heap, q#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), q#0, _module.Node.rank)): int;
    assert {:id "id917"} r#0 != null;
    assume true;
    assert {:id "id918"} r#0 != null;
    assert {:id "id919"} r#0 == null || old($Alloc)[r#0];
    assume true;
    assume {:id "id920"} $Unbox(read($Heap, r#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), r#0, _module.Node.val)): int + 1;
    assert {:id "id921"} r#0 != null;
    assume true;
    assert {:id "id922"} r#0 != null;
    assert {:id "id923"} r#0 == null || old($Alloc)[r#0];
    assume true;
    assume {:id "id924"} $Unbox(read($Heap, r#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), r#0, _module.Node.tag)): int;
    assert {:id "id925"} r#0 != null;
    assume true;
    assert {:id "id926"} r#0 != null;
    assert {:id "id927"} r#0 == null || old($Alloc)[r#0];
    assume true;
    assume {:id "id928"} $Unbox(read($Heap, r#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), r#0, _module.Node.score)): int;
    assert {:id "id929"} r#0 != null;
    assume true;
    assert {:id "id930"} r#0 != null;
    assert {:id "id931"} r#0 == null || old($Alloc)[r#0];
    assume true;
    assume {:id "id932"} $Unbox(read($Heap, r#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), r#0, _module.Node.rank)): int;
}



procedure {:verboseName "CrossBump (call)"} Call$$_module.__default.CrossBump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    p#0: ref where $Is(p#0, Tclass._module.Node()) && (p#0 == null || $Alloc[p#0]), 
    q#0: ref where $Is(q#0, Tclass._module.Node()) && (q#0 == null || $Alloc[q#0]), 
    r#0: ref where $Is(r#0, Tclass._module.Node()) && (r#0 == null || $Alloc[r#0]));
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id933"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id934"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id935"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id936"} p#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id937"} p#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id938"} q#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id939"} a#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id940"} a#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id941"} a#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id942"} b#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id943"} b#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id944"} b#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id945"} c#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id946"} c#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id947"} c#0 != r#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id948"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id949"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id950"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id951"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id952"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id953"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id954"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id955"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id956"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id957"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id958"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id959"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id960"} $Unbox(read($Heap, p#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id961"} $Unbox(read($Heap, p#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id962"} $Unbox(read($Heap, p#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id963"} $Unbox(read($Heap, p#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id964"} $Unbox(read($Heap, q#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id965"} $Unbox(read($Heap, q#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id966"} $Unbox(read($Heap, q#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id967"} $Unbox(read($Heap, q#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id968"} $Unbox(read($Heap, r#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id969"} $Unbox(read($Heap, r#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id970"} $Unbox(read($Heap, r#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id971"} $Unbox(read($Heap, r#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.rank)): int;



procedure {:verboseName "CrossBump (correctness)"} Impl$$_module.__default.CrossBump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    p#0: ref where $Is(p#0, Tclass._module.Node()) && (p#0 == null || $Alloc[p#0]), 
    q#0: ref where $Is(q#0, Tclass._module.Node()) && (q#0 == null || $Alloc[q#0]), 
    r#0: ref where $Is(r#0, Tclass._module.Node()) && (r#0 == null || $Alloc[r#0]))
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id972"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id973"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id974"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id975"} p#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id976"} p#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id977"} q#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id978"} a#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id979"} a#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id980"} a#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id981"} b#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id982"} b#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id983"} b#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id984"} c#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id985"} c#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id986"} c#0 != r#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id987"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id988"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id989"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id990"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id991"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id992"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id993"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id994"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id995"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id996"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id997"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id998"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id999"} $Unbox(read($Heap, p#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id1000"} $Unbox(read($Heap, p#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1001"} $Unbox(read($Heap, p#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1002"} $Unbox(read($Heap, p#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1003"} $Unbox(read($Heap, q#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id1004"} $Unbox(read($Heap, q#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1005"} $Unbox(read($Heap, q#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1006"} $Unbox(read($Heap, q#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1007"} $Unbox(read($Heap, r#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id1008"} $Unbox(read($Heap, r#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1009"} $Unbox(read($Heap, r#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1010"} $Unbox(read($Heap, r#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.rank)): int;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "CrossBump (correctness)"} Impl$$_module.__default.CrossBump(a#0: ref, b#0: ref, c#0: ref, p#0: ref, q#0: ref, r#0: ref)
   returns ($_reverifyPost: bool)
{
  var $rhs#0: int;
  var $rhs#1: int;
  var $rhs#2: int;
  var $rhs#3: int;
  var $rhs#4: int;
  var $rhs#5: int;

    // AddMethodImpl: CrossBump, Impl$$_module.__default.CrossBump
    assume {:captureState "Test/arith.dfy(106,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(107,9)
    assert {:id "id1011"} a#0 != null;
    assume true;
    assume true;
    assert {:id "id1012"} a#0 != null;
    assume true;
    assume true;
    $rhs#0 := $Unbox(read($Heap, a#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, a#0, _module.Node.val, $Box($rhs#0));
    assume true;
    assume {:captureState "Test/arith.dfy(107,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(108,9)
    assert {:id "id1015"} b#0 != null;
    assume true;
    assume true;
    assert {:id "id1016"} b#0 != null;
    assume true;
    assume true;
    $rhs#1 := $Unbox(read($Heap, b#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, b#0, _module.Node.val, $Box($rhs#1));
    assume true;
    assume {:captureState "Test/arith.dfy(108,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(109,9)
    assert {:id "id1019"} c#0 != null;
    assume true;
    assume true;
    assert {:id "id1020"} c#0 != null;
    assume true;
    assume true;
    $rhs#2 := $Unbox(read($Heap, c#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, c#0, _module.Node.val, $Box($rhs#2));
    assume true;
    assume {:captureState "Test/arith.dfy(109,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(110,9)
    assert {:id "id1023"} p#0 != null;
    assume true;
    assume true;
    assert {:id "id1024"} p#0 != null;
    assume true;
    assume true;
    $rhs#3 := $Unbox(read($Heap, p#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, p#0, _module.Node.val, $Box($rhs#3));
    assume true;
    assume {:captureState "Test/arith.dfy(110,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(111,9)
    assert {:id "id1027"} q#0 != null;
    assume true;
    assume true;
    assert {:id "id1028"} q#0 != null;
    assume true;
    assume true;
    $rhs#4 := $Unbox(read($Heap, q#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, q#0, _module.Node.val, $Box($rhs#4));
    assume true;
    assume {:captureState "Test/arith.dfy(111,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(112,9)
    assert {:id "id1031"} r#0 != null;
    assume true;
    assume true;
    assert {:id "id1032"} r#0 != null;
    assume true;
    assume true;
    $rhs#5 := $Unbox(read($Heap, r#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, r#0, _module.Node.val, $Box($rhs#5));
    assume true;
    assume {:captureState "Test/arith.dfy(112,20)"} true;
}



procedure {:verboseName "BumpN (well-formedness)"} CheckWellFormed$$_module.__default.BumpN(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]), 
    n#0: int);
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "BumpN (well-formedness)"} CheckWellFormed$$_module.__default.BumpN(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref, n#0: int)
{

    // AddMethodImpl: BumpN, CheckWellFormed$$_module.__default.BumpN
    assume {:captureState "Test/arith.dfy(119,7): initial state"} true;
    assume {:id "id1035"} n#0 >= LitInt(0);
    assume {:id "id1036"} a#0 != b#0;
    assume {:id "id1037"} a#0 != c#0;
    assume {:id "id1038"} a#0 != d#0;
    assume {:id "id1039"} a#0 != e#0;
    assume {:id "id1040"} a#0 != f#0;
    assume {:id "id1041"} b#0 != c#0;
    assume {:id "id1042"} b#0 != d#0;
    assume {:id "id1043"} b#0 != e#0;
    assume {:id "id1044"} b#0 != f#0;
    assume {:id "id1045"} c#0 != d#0;
    assume {:id "id1046"} c#0 != e#0;
    assume {:id "id1047"} c#0 != f#0;
    assume {:id "id1048"} d#0 != e#0;
    assume {:id "id1049"} d#0 != f#0;
    assume {:id "id1050"} e#0 != f#0;
    havoc $Heap;
    assume {:captureState "Test/arith.dfy(126,86): post-state"} true;
    assert {:id "id1051"} a#0 != null;
    assume true;
    assert {:id "id1052"} a#0 != null;
    assert {:id "id1053"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id1054"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
    assert {:id "id1055"} a#0 != null;
    assume true;
    assert {:id "id1056"} a#0 != null;
    assert {:id "id1057"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id1058"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id1059"} a#0 != null;
    assume true;
    assert {:id "id1060"} a#0 != null;
    assert {:id "id1061"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id1062"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id1063"} a#0 != null;
    assume true;
    assert {:id "id1064"} a#0 != null;
    assert {:id "id1065"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id1066"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
    assert {:id "id1067"} b#0 != null;
    assume true;
    assert {:id "id1068"} b#0 != null;
    assert {:id "id1069"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id1070"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
    assert {:id "id1071"} b#0 != null;
    assume true;
    assert {:id "id1072"} b#0 != null;
    assert {:id "id1073"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id1074"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id1075"} b#0 != null;
    assume true;
    assert {:id "id1076"} b#0 != null;
    assert {:id "id1077"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id1078"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id1079"} b#0 != null;
    assume true;
    assert {:id "id1080"} b#0 != null;
    assert {:id "id1081"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id1082"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
    assert {:id "id1083"} c#0 != null;
    assume true;
    assert {:id "id1084"} c#0 != null;
    assert {:id "id1085"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id1086"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
    assert {:id "id1087"} c#0 != null;
    assume true;
    assert {:id "id1088"} c#0 != null;
    assert {:id "id1089"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id1090"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id1091"} c#0 != null;
    assume true;
    assert {:id "id1092"} c#0 != null;
    assert {:id "id1093"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id1094"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id1095"} c#0 != null;
    assume true;
    assert {:id "id1096"} c#0 != null;
    assert {:id "id1097"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id1098"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
    assert {:id "id1099"} d#0 != null;
    assume true;
    assert {:id "id1100"} d#0 != null;
    assert {:id "id1101"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id1102"} $Unbox(read($Heap, d#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
    assert {:id "id1103"} d#0 != null;
    assume true;
    assert {:id "id1104"} d#0 != null;
    assert {:id "id1105"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id1106"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
    assert {:id "id1107"} d#0 != null;
    assume true;
    assert {:id "id1108"} d#0 != null;
    assert {:id "id1109"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id1110"} $Unbox(read($Heap, d#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
    assert {:id "id1111"} d#0 != null;
    assume true;
    assert {:id "id1112"} d#0 != null;
    assert {:id "id1113"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id1114"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
    assert {:id "id1115"} e#0 != null;
    assume true;
    assert {:id "id1116"} e#0 != null;
    assert {:id "id1117"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id1118"} $Unbox(read($Heap, e#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
    assert {:id "id1119"} e#0 != null;
    assume true;
    assert {:id "id1120"} e#0 != null;
    assert {:id "id1121"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id1122"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
    assert {:id "id1123"} e#0 != null;
    assume true;
    assert {:id "id1124"} e#0 != null;
    assert {:id "id1125"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id1126"} $Unbox(read($Heap, e#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
    assert {:id "id1127"} e#0 != null;
    assume true;
    assert {:id "id1128"} e#0 != null;
    assert {:id "id1129"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id1130"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
    assert {:id "id1131"} f#0 != null;
    assume true;
    assert {:id "id1132"} f#0 != null;
    assert {:id "id1133"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id1134"} $Unbox(read($Heap, f#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
    assert {:id "id1135"} f#0 != null;
    assume true;
    assert {:id "id1136"} f#0 != null;
    assert {:id "id1137"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id1138"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
    assert {:id "id1139"} f#0 != null;
    assume true;
    assert {:id "id1140"} f#0 != null;
    assert {:id "id1141"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id1142"} $Unbox(read($Heap, f#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
    assert {:id "id1143"} f#0 != null;
    assume true;
    assert {:id "id1144"} f#0 != null;
    assert {:id "id1145"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id1146"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
}



procedure {:verboseName "BumpN (call)"} Call$$_module.__default.BumpN(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]), 
    n#0: int);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id1147"} n#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id1148"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id1149"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1150"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1151"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1152"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1153"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1154"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1155"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1156"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1157"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1158"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1159"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1160"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1161"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1162"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id1163"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1164"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1165"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1166"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1167"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1168"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1169"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1170"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1171"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1172"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1173"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1174"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1175"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1176"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1177"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1178"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1179"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1180"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1181"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1182"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1183"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1184"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1185"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1186"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;



procedure {:verboseName "BumpN (correctness)"} Impl$$_module.__default.BumpN(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]), 
    n#0: int)
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id1187"} n#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id1188"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id1189"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1190"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1191"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1192"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1193"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1194"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1195"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1196"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1197"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1198"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1199"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1200"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1201"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1202"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id1203"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1204"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1205"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1206"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1207"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1208"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1209"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1210"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1211"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1212"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1213"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1214"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1215"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1216"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1217"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1218"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1219"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1220"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1221"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1222"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1223"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(2), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1224"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1225"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1226"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "BumpN (correctness)"} Impl$$_module.__default.BumpN(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref, n#0: int)
   returns ($_reverifyPost: bool)
{
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $PreLoopAlloc$loop#0: [ref]bool;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var a##0_0: ref;
  var b##0_0: ref;
  var c##0_0: ref;
  var d##0_0: ref;
  var e##0_0: ref;
  var f##0_0: ref;
  var $PreCallHeap#0_0: Heap;
  var $PreCallAlloc#0_0: [ref]bool;

    // AddMethodImpl: BumpN, Impl$$_module.__default.BumpN
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
    $PreLoopAlloc$loop#0 := $Alloc;
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
      invariant {:id "id1229"} $w$loop#0 ==> LitInt(0) <= i#0;
      invariant {:id "id1230"} $w$loop#0 ==> i#0 <= n#0;
      free invariant true;
      invariant {:id "id1244"} $w$loop#0
         ==> $Unbox(read($Heap, a#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(2), i#0);
      invariant {:id "id1245"} $w$loop#0
         ==> $Unbox(read($Heap, a#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
      invariant {:id "id1246"} $w$loop#0
         ==> $Unbox(read($Heap, a#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
      invariant {:id "id1247"} $w$loop#0
         ==> $Unbox(read($Heap, a#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1261"} $w$loop#0
         ==> $Unbox(read($Heap, b#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(2), i#0);
      invariant {:id "id1262"} $w$loop#0
         ==> $Unbox(read($Heap, b#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
      invariant {:id "id1263"} $w$loop#0
         ==> $Unbox(read($Heap, b#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
      invariant {:id "id1264"} $w$loop#0
         ==> $Unbox(read($Heap, b#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1278"} $w$loop#0
         ==> $Unbox(read($Heap, c#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(2), i#0);
      invariant {:id "id1279"} $w$loop#0
         ==> $Unbox(read($Heap, c#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
      invariant {:id "id1280"} $w$loop#0
         ==> $Unbox(read($Heap, c#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
      invariant {:id "id1281"} $w$loop#0
         ==> $Unbox(read($Heap, c#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1295"} $w$loop#0
         ==> $Unbox(read($Heap, d#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(2), i#0);
      invariant {:id "id1296"} $w$loop#0
         ==> $Unbox(read($Heap, d#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
      invariant {:id "id1297"} $w$loop#0
         ==> $Unbox(read($Heap, d#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
      invariant {:id "id1298"} $w$loop#0
         ==> $Unbox(read($Heap, d#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1312"} $w$loop#0
         ==> $Unbox(read($Heap, e#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(2), i#0);
      invariant {:id "id1313"} $w$loop#0
         ==> $Unbox(read($Heap, e#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
      invariant {:id "id1314"} $w$loop#0
         ==> $Unbox(read($Heap, e#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
      invariant {:id "id1315"} $w$loop#0
         ==> $Unbox(read($Heap, e#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1329"} $w$loop#0
         ==> $Unbox(read($Heap, f#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(2), i#0);
      invariant {:id "id1330"} $w$loop#0
         ==> $Unbox(read($Heap, f#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
      invariant {:id "id1331"} $w$loop#0
         ==> $Unbox(read($Heap, f#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
      invariant {:id "id1332"} $w$loop#0
         ==> $Unbox(read($Heap, f#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
      free invariant a#0 != null
           && a#0 != a#0
           && a#0 != b#0
           && a#0 != c#0
           && a#0 != d#0
           && a#0 != e#0
           && a#0 != f#0
         ==> read($PreLoopHeap$loop#0, a#0, _module.Node.val)
           == read($PreLoopHeap$loop#0, a#0, _module.Node.val);
      free invariant a#0 != null
           && a#0 != a#0
           && a#0 != b#0
           && a#0 != c#0
           && a#0 != d#0
           && a#0 != e#0
           && a#0 != f#0
         ==> read($PreLoopHeap$loop#0, a#0, _module.Node.tag)
           == read($PreLoopHeap$loop#0, a#0, _module.Node.tag);
      free invariant a#0 != null
           && a#0 != a#0
           && a#0 != b#0
           && a#0 != c#0
           && a#0 != d#0
           && a#0 != e#0
           && a#0 != f#0
         ==> read($PreLoopHeap$loop#0, a#0, _module.Node.score)
           == read($PreLoopHeap$loop#0, a#0, _module.Node.score);
      free invariant a#0 != null
           && a#0 != a#0
           && a#0 != b#0
           && a#0 != c#0
           && a#0 != d#0
           && a#0 != e#0
           && a#0 != f#0
         ==> read($PreLoopHeap$loop#0, a#0, _module.Node.rank)
           == read($PreLoopHeap$loop#0, a#0, _module.Node.rank);
      free invariant b#0 != null
           && b#0 != a#0
           && b#0 != b#0
           && b#0 != c#0
           && b#0 != d#0
           && b#0 != e#0
           && b#0 != f#0
         ==> read($PreLoopHeap$loop#0, b#0, _module.Node.val)
           == read($PreLoopHeap$loop#0, b#0, _module.Node.val);
      free invariant b#0 != null
           && b#0 != a#0
           && b#0 != b#0
           && b#0 != c#0
           && b#0 != d#0
           && b#0 != e#0
           && b#0 != f#0
         ==> read($PreLoopHeap$loop#0, b#0, _module.Node.tag)
           == read($PreLoopHeap$loop#0, b#0, _module.Node.tag);
      free invariant b#0 != null
           && b#0 != a#0
           && b#0 != b#0
           && b#0 != c#0
           && b#0 != d#0
           && b#0 != e#0
           && b#0 != f#0
         ==> read($PreLoopHeap$loop#0, b#0, _module.Node.score)
           == read($PreLoopHeap$loop#0, b#0, _module.Node.score);
      free invariant b#0 != null
           && b#0 != a#0
           && b#0 != b#0
           && b#0 != c#0
           && b#0 != d#0
           && b#0 != e#0
           && b#0 != f#0
         ==> read($PreLoopHeap$loop#0, b#0, _module.Node.rank)
           == read($PreLoopHeap$loop#0, b#0, _module.Node.rank);
      free invariant c#0 != null
           && c#0 != a#0
           && c#0 != b#0
           && c#0 != c#0
           && c#0 != d#0
           && c#0 != e#0
           && c#0 != f#0
         ==> read($PreLoopHeap$loop#0, c#0, _module.Node.val)
           == read($PreLoopHeap$loop#0, c#0, _module.Node.val);
      free invariant c#0 != null
           && c#0 != a#0
           && c#0 != b#0
           && c#0 != c#0
           && c#0 != d#0
           && c#0 != e#0
           && c#0 != f#0
         ==> read($PreLoopHeap$loop#0, c#0, _module.Node.tag)
           == read($PreLoopHeap$loop#0, c#0, _module.Node.tag);
      free invariant c#0 != null
           && c#0 != a#0
           && c#0 != b#0
           && c#0 != c#0
           && c#0 != d#0
           && c#0 != e#0
           && c#0 != f#0
         ==> read($PreLoopHeap$loop#0, c#0, _module.Node.score)
           == read($PreLoopHeap$loop#0, c#0, _module.Node.score);
      free invariant c#0 != null
           && c#0 != a#0
           && c#0 != b#0
           && c#0 != c#0
           && c#0 != d#0
           && c#0 != e#0
           && c#0 != f#0
         ==> read($PreLoopHeap$loop#0, c#0, _module.Node.rank)
           == read($PreLoopHeap$loop#0, c#0, _module.Node.rank);
      free invariant d#0 != null
           && d#0 != a#0
           && d#0 != b#0
           && d#0 != c#0
           && d#0 != d#0
           && d#0 != e#0
           && d#0 != f#0
         ==> read($PreLoopHeap$loop#0, d#0, _module.Node.val)
           == read($PreLoopHeap$loop#0, d#0, _module.Node.val);
      free invariant d#0 != null
           && d#0 != a#0
           && d#0 != b#0
           && d#0 != c#0
           && d#0 != d#0
           && d#0 != e#0
           && d#0 != f#0
         ==> read($PreLoopHeap$loop#0, d#0, _module.Node.tag)
           == read($PreLoopHeap$loop#0, d#0, _module.Node.tag);
      free invariant d#0 != null
           && d#0 != a#0
           && d#0 != b#0
           && d#0 != c#0
           && d#0 != d#0
           && d#0 != e#0
           && d#0 != f#0
         ==> read($PreLoopHeap$loop#0, d#0, _module.Node.score)
           == read($PreLoopHeap$loop#0, d#0, _module.Node.score);
      free invariant d#0 != null
           && d#0 != a#0
           && d#0 != b#0
           && d#0 != c#0
           && d#0 != d#0
           && d#0 != e#0
           && d#0 != f#0
         ==> read($PreLoopHeap$loop#0, d#0, _module.Node.rank)
           == read($PreLoopHeap$loop#0, d#0, _module.Node.rank);
      free invariant e#0 != null
           && e#0 != a#0
           && e#0 != b#0
           && e#0 != c#0
           && e#0 != d#0
           && e#0 != e#0
           && e#0 != f#0
         ==> read($PreLoopHeap$loop#0, e#0, _module.Node.val)
           == read($PreLoopHeap$loop#0, e#0, _module.Node.val);
      free invariant e#0 != null
           && e#0 != a#0
           && e#0 != b#0
           && e#0 != c#0
           && e#0 != d#0
           && e#0 != e#0
           && e#0 != f#0
         ==> read($PreLoopHeap$loop#0, e#0, _module.Node.tag)
           == read($PreLoopHeap$loop#0, e#0, _module.Node.tag);
      free invariant e#0 != null
           && e#0 != a#0
           && e#0 != b#0
           && e#0 != c#0
           && e#0 != d#0
           && e#0 != e#0
           && e#0 != f#0
         ==> read($PreLoopHeap$loop#0, e#0, _module.Node.score)
           == read($PreLoopHeap$loop#0, e#0, _module.Node.score);
      free invariant e#0 != null
           && e#0 != a#0
           && e#0 != b#0
           && e#0 != c#0
           && e#0 != d#0
           && e#0 != e#0
           && e#0 != f#0
         ==> read($PreLoopHeap$loop#0, e#0, _module.Node.rank)
           == read($PreLoopHeap$loop#0, e#0, _module.Node.rank);
      free invariant f#0 != null
           && f#0 != a#0
           && f#0 != b#0
           && f#0 != c#0
           && f#0 != d#0
           && f#0 != e#0
           && f#0 != f#0
         ==> read($PreLoopHeap$loop#0, f#0, _module.Node.val)
           == read($PreLoopHeap$loop#0, f#0, _module.Node.val);
      free invariant f#0 != null
           && f#0 != a#0
           && f#0 != b#0
           && f#0 != c#0
           && f#0 != d#0
           && f#0 != e#0
           && f#0 != f#0
         ==> read($PreLoopHeap$loop#0, f#0, _module.Node.tag)
           == read($PreLoopHeap$loop#0, f#0, _module.Node.tag);
      free invariant f#0 != null
           && f#0 != a#0
           && f#0 != b#0
           && f#0 != c#0
           && f#0 != d#0
           && f#0 != e#0
           && f#0 != f#0
         ==> read($PreLoopHeap$loop#0, f#0, _module.Node.score)
           == read($PreLoopHeap$loop#0, f#0, _module.Node.score);
      free invariant f#0 != null
           && f#0 != a#0
           && f#0 != b#0
           && f#0 != c#0
           && f#0 != d#0
           && f#0 != e#0
           && f#0 != f#0
         ==> read($PreLoopHeap$loop#0, f#0, _module.Node.rank)
           == read($PreLoopHeap$loop#0, f#0, _module.Node.rank);
      free invariant n#0 - i#0 <= $decr_init$loop#00;
    {
        assume {:captureState "Test/arith.dfy(134,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (LitInt(0) <= i#0)
            {
            }

            assume true;
            assume {:id "id1228"} LitInt(0) <= i#0 && i#0 <= n#0;
            assert {:id "id1231"} {:subsumption 0} a#0 != null;
            assume true;
            assert {:id "id1232"} {:subsumption 0} a#0 != null;
            assert {:id "id1233"} a#0 == null || old($Alloc)[a#0];
            assume true;
            if ($Unbox(read($Heap, a#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(2), i#0))
            {
                assert {:id "id1234"} {:subsumption 0} a#0 != null;
                assume true;
                assert {:id "id1235"} {:subsumption 0} a#0 != null;
                assert {:id "id1236"} a#0 == null || old($Alloc)[a#0];
                assume true;
            }

            if ($Unbox(read($Heap, a#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, a#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int)
            {
                assert {:id "id1237"} {:subsumption 0} a#0 != null;
                assume true;
                assert {:id "id1238"} {:subsumption 0} a#0 != null;
                assert {:id "id1239"} a#0 == null || old($Alloc)[a#0];
                assume true;
            }

            if ($Unbox(read($Heap, a#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, a#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int
               && $Unbox(read($Heap, a#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.score)): int)
            {
                assert {:id "id1240"} {:subsumption 0} a#0 != null;
                assume true;
                assert {:id "id1241"} {:subsumption 0} a#0 != null;
                assert {:id "id1242"} a#0 == null || old($Alloc)[a#0];
                assume true;
            }

            assume true;
            assume {:id "id1243"} $Unbox(read($Heap, a#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, a#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int
               && $Unbox(read($Heap, a#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.score)): int
               && $Unbox(read($Heap, a#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
            assert {:id "id1248"} {:subsumption 0} b#0 != null;
            assume true;
            assert {:id "id1249"} {:subsumption 0} b#0 != null;
            assert {:id "id1250"} b#0 == null || old($Alloc)[b#0];
            assume true;
            if ($Unbox(read($Heap, b#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(2), i#0))
            {
                assert {:id "id1251"} {:subsumption 0} b#0 != null;
                assume true;
                assert {:id "id1252"} {:subsumption 0} b#0 != null;
                assert {:id "id1253"} b#0 == null || old($Alloc)[b#0];
                assume true;
            }

            if ($Unbox(read($Heap, b#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, b#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int)
            {
                assert {:id "id1254"} {:subsumption 0} b#0 != null;
                assume true;
                assert {:id "id1255"} {:subsumption 0} b#0 != null;
                assert {:id "id1256"} b#0 == null || old($Alloc)[b#0];
                assume true;
            }

            if ($Unbox(read($Heap, b#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, b#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int
               && $Unbox(read($Heap, b#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.score)): int)
            {
                assert {:id "id1257"} {:subsumption 0} b#0 != null;
                assume true;
                assert {:id "id1258"} {:subsumption 0} b#0 != null;
                assert {:id "id1259"} b#0 == null || old($Alloc)[b#0];
                assume true;
            }

            assume true;
            assume {:id "id1260"} $Unbox(read($Heap, b#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, b#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int
               && $Unbox(read($Heap, b#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.score)): int
               && $Unbox(read($Heap, b#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
            assert {:id "id1265"} {:subsumption 0} c#0 != null;
            assume true;
            assert {:id "id1266"} {:subsumption 0} c#0 != null;
            assert {:id "id1267"} c#0 == null || old($Alloc)[c#0];
            assume true;
            if ($Unbox(read($Heap, c#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(2), i#0))
            {
                assert {:id "id1268"} {:subsumption 0} c#0 != null;
                assume true;
                assert {:id "id1269"} {:subsumption 0} c#0 != null;
                assert {:id "id1270"} c#0 == null || old($Alloc)[c#0];
                assume true;
            }

            if ($Unbox(read($Heap, c#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, c#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int)
            {
                assert {:id "id1271"} {:subsumption 0} c#0 != null;
                assume true;
                assert {:id "id1272"} {:subsumption 0} c#0 != null;
                assert {:id "id1273"} c#0 == null || old($Alloc)[c#0];
                assume true;
            }

            if ($Unbox(read($Heap, c#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, c#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int
               && $Unbox(read($Heap, c#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.score)): int)
            {
                assert {:id "id1274"} {:subsumption 0} c#0 != null;
                assume true;
                assert {:id "id1275"} {:subsumption 0} c#0 != null;
                assert {:id "id1276"} c#0 == null || old($Alloc)[c#0];
                assume true;
            }

            assume true;
            assume {:id "id1277"} $Unbox(read($Heap, c#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, c#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int
               && $Unbox(read($Heap, c#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.score)): int
               && $Unbox(read($Heap, c#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
            assert {:id "id1282"} {:subsumption 0} d#0 != null;
            assume true;
            assert {:id "id1283"} {:subsumption 0} d#0 != null;
            assert {:id "id1284"} d#0 == null || old($Alloc)[d#0];
            assume true;
            if ($Unbox(read($Heap, d#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(2), i#0))
            {
                assert {:id "id1285"} {:subsumption 0} d#0 != null;
                assume true;
                assert {:id "id1286"} {:subsumption 0} d#0 != null;
                assert {:id "id1287"} d#0 == null || old($Alloc)[d#0];
                assume true;
            }

            if ($Unbox(read($Heap, d#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, d#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int)
            {
                assert {:id "id1288"} {:subsumption 0} d#0 != null;
                assume true;
                assert {:id "id1289"} {:subsumption 0} d#0 != null;
                assert {:id "id1290"} d#0 == null || old($Alloc)[d#0];
                assume true;
            }

            if ($Unbox(read($Heap, d#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, d#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int
               && $Unbox(read($Heap, d#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.score)): int)
            {
                assert {:id "id1291"} {:subsumption 0} d#0 != null;
                assume true;
                assert {:id "id1292"} {:subsumption 0} d#0 != null;
                assert {:id "id1293"} d#0 == null || old($Alloc)[d#0];
                assume true;
            }

            assume true;
            assume {:id "id1294"} $Unbox(read($Heap, d#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, d#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int
               && $Unbox(read($Heap, d#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.score)): int
               && $Unbox(read($Heap, d#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
            assert {:id "id1299"} {:subsumption 0} e#0 != null;
            assume true;
            assert {:id "id1300"} {:subsumption 0} e#0 != null;
            assert {:id "id1301"} e#0 == null || old($Alloc)[e#0];
            assume true;
            if ($Unbox(read($Heap, e#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(2), i#0))
            {
                assert {:id "id1302"} {:subsumption 0} e#0 != null;
                assume true;
                assert {:id "id1303"} {:subsumption 0} e#0 != null;
                assert {:id "id1304"} e#0 == null || old($Alloc)[e#0];
                assume true;
            }

            if ($Unbox(read($Heap, e#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, e#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int)
            {
                assert {:id "id1305"} {:subsumption 0} e#0 != null;
                assume true;
                assert {:id "id1306"} {:subsumption 0} e#0 != null;
                assert {:id "id1307"} e#0 == null || old($Alloc)[e#0];
                assume true;
            }

            if ($Unbox(read($Heap, e#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, e#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int
               && $Unbox(read($Heap, e#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.score)): int)
            {
                assert {:id "id1308"} {:subsumption 0} e#0 != null;
                assume true;
                assert {:id "id1309"} {:subsumption 0} e#0 != null;
                assert {:id "id1310"} e#0 == null || old($Alloc)[e#0];
                assume true;
            }

            assume true;
            assume {:id "id1311"} $Unbox(read($Heap, e#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, e#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int
               && $Unbox(read($Heap, e#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.score)): int
               && $Unbox(read($Heap, e#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
            assert {:id "id1316"} {:subsumption 0} f#0 != null;
            assume true;
            assert {:id "id1317"} {:subsumption 0} f#0 != null;
            assert {:id "id1318"} f#0 == null || old($Alloc)[f#0];
            assume true;
            if ($Unbox(read($Heap, f#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(2), i#0))
            {
                assert {:id "id1319"} {:subsumption 0} f#0 != null;
                assume true;
                assert {:id "id1320"} {:subsumption 0} f#0 != null;
                assert {:id "id1321"} f#0 == null || old($Alloc)[f#0];
                assume true;
            }

            if ($Unbox(read($Heap, f#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, f#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int)
            {
                assert {:id "id1322"} {:subsumption 0} f#0 != null;
                assume true;
                assert {:id "id1323"} {:subsumption 0} f#0 != null;
                assert {:id "id1324"} f#0 == null || old($Alloc)[f#0];
                assume true;
            }

            if ($Unbox(read($Heap, f#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(2), i#0)
               && $Unbox(read($Heap, f#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int
               && $Unbox(read($Heap, f#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.score)): int)
            {
                assert {:id "id1325"} {:subsumption 0} f#0 != null;
                assume true;
                assert {:id "id1326"} {:subsumption 0} f#0 != null;
                assert {:id "id1327"} f#0 == null || old($Alloc)[f#0];
                assume true;
            }

            assume true;
            assume {:id "id1328"} $Unbox(read($Heap, f#0, _module.Node.val)): int
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
        $PreCallHeap#0_0 := $Heap;
        $PreCallAlloc#0_0 := $Alloc;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assert {:id "id1333"} a##0_0 == a#0
           || a##0_0 == b#0
           || a##0_0 == c#0
           || a##0_0 == d#0
           || a##0_0 == e#0
           || a##0_0 == f#0
           || !old($Alloc)[a##0_0];
        assert {:id "id1334"} b##0_0 == a#0
           || b##0_0 == b#0
           || b##0_0 == c#0
           || b##0_0 == d#0
           || b##0_0 == e#0
           || b##0_0 == f#0
           || !old($Alloc)[b##0_0];
        assert {:id "id1335"} c##0_0 == a#0
           || c##0_0 == b#0
           || c##0_0 == c#0
           || c##0_0 == d#0
           || c##0_0 == e#0
           || c##0_0 == f#0
           || !old($Alloc)[c##0_0];
        assert {:id "id1336"} d##0_0 == a#0
           || d##0_0 == b#0
           || d##0_0 == c#0
           || d##0_0 == d#0
           || d##0_0 == e#0
           || d##0_0 == f#0
           || !old($Alloc)[d##0_0];
        assert {:id "id1337"} e##0_0 == a#0
           || e##0_0 == b#0
           || e##0_0 == c#0
           || e##0_0 == d#0
           || e##0_0 == e#0
           || e##0_0 == f#0
           || !old($Alloc)[e##0_0];
        assert {:id "id1338"} f##0_0 == a#0
           || f##0_0 == b#0
           || f##0_0 == c#0
           || f##0_0 == d#0
           || f##0_0 == e#0
           || f##0_0 == f#0
           || !old($Alloc)[f##0_0];
        call {:id "id1339"} Call$$_module.__default.DoubleBump(a##0_0, b##0_0, c##0_0, d##0_0, e##0_0, f##0_0);
        // qf-call-frame DoubleBump: supports=12 reads=48 modified=6
        assume a#0 != null
             && a#0 != a#0
             && a#0 != b#0
             && a#0 != c#0
             && a#0 != d#0
             && a#0 != e#0
             && a#0 != f#0
           ==> read($Heap, a#0, _module.Node.val)
             == read($PreCallHeap#0_0, a#0, _module.Node.val);
        assume a#0 != null
             && a#0 != a#0
             && a#0 != b#0
             && a#0 != c#0
             && a#0 != d#0
             && a#0 != e#0
             && a#0 != f#0
           ==> read($Heap, a#0, _module.Node.tag)
             == read($PreCallHeap#0_0, a#0, _module.Node.tag);
        assume a#0 != null
             && a#0 != a#0
             && a#0 != b#0
             && a#0 != c#0
             && a#0 != d#0
             && a#0 != e#0
             && a#0 != f#0
           ==> read($Heap, a#0, _module.Node.score)
             == read($PreCallHeap#0_0, a#0, _module.Node.score);
        assume a#0 != null
             && a#0 != a#0
             && a#0 != b#0
             && a#0 != c#0
             && a#0 != d#0
             && a#0 != e#0
             && a#0 != f#0
           ==> read($Heap, a#0, _module.Node.rank)
             == read($PreCallHeap#0_0, a#0, _module.Node.rank);
        assume b#0 != null
             && b#0 != a#0
             && b#0 != b#0
             && b#0 != c#0
             && b#0 != d#0
             && b#0 != e#0
             && b#0 != f#0
           ==> read($Heap, b#0, _module.Node.val)
             == read($PreCallHeap#0_0, b#0, _module.Node.val);
        assume b#0 != null
             && b#0 != a#0
             && b#0 != b#0
             && b#0 != c#0
             && b#0 != d#0
             && b#0 != e#0
             && b#0 != f#0
           ==> read($Heap, b#0, _module.Node.tag)
             == read($PreCallHeap#0_0, b#0, _module.Node.tag);
        assume b#0 != null
             && b#0 != a#0
             && b#0 != b#0
             && b#0 != c#0
             && b#0 != d#0
             && b#0 != e#0
             && b#0 != f#0
           ==> read($Heap, b#0, _module.Node.score)
             == read($PreCallHeap#0_0, b#0, _module.Node.score);
        assume b#0 != null
             && b#0 != a#0
             && b#0 != b#0
             && b#0 != c#0
             && b#0 != d#0
             && b#0 != e#0
             && b#0 != f#0
           ==> read($Heap, b#0, _module.Node.rank)
             == read($PreCallHeap#0_0, b#0, _module.Node.rank);
        assume c#0 != null
             && c#0 != a#0
             && c#0 != b#0
             && c#0 != c#0
             && c#0 != d#0
             && c#0 != e#0
             && c#0 != f#0
           ==> read($Heap, c#0, _module.Node.val)
             == read($PreCallHeap#0_0, c#0, _module.Node.val);
        assume c#0 != null
             && c#0 != a#0
             && c#0 != b#0
             && c#0 != c#0
             && c#0 != d#0
             && c#0 != e#0
             && c#0 != f#0
           ==> read($Heap, c#0, _module.Node.tag)
             == read($PreCallHeap#0_0, c#0, _module.Node.tag);
        assume c#0 != null
             && c#0 != a#0
             && c#0 != b#0
             && c#0 != c#0
             && c#0 != d#0
             && c#0 != e#0
             && c#0 != f#0
           ==> read($Heap, c#0, _module.Node.score)
             == read($PreCallHeap#0_0, c#0, _module.Node.score);
        assume c#0 != null
             && c#0 != a#0
             && c#0 != b#0
             && c#0 != c#0
             && c#0 != d#0
             && c#0 != e#0
             && c#0 != f#0
           ==> read($Heap, c#0, _module.Node.rank)
             == read($PreCallHeap#0_0, c#0, _module.Node.rank);
        assume d#0 != null
             && d#0 != a#0
             && d#0 != b#0
             && d#0 != c#0
             && d#0 != d#0
             && d#0 != e#0
             && d#0 != f#0
           ==> read($Heap, d#0, _module.Node.val)
             == read($PreCallHeap#0_0, d#0, _module.Node.val);
        assume d#0 != null
             && d#0 != a#0
             && d#0 != b#0
             && d#0 != c#0
             && d#0 != d#0
             && d#0 != e#0
             && d#0 != f#0
           ==> read($Heap, d#0, _module.Node.tag)
             == read($PreCallHeap#0_0, d#0, _module.Node.tag);
        assume d#0 != null
             && d#0 != a#0
             && d#0 != b#0
             && d#0 != c#0
             && d#0 != d#0
             && d#0 != e#0
             && d#0 != f#0
           ==> read($Heap, d#0, _module.Node.score)
             == read($PreCallHeap#0_0, d#0, _module.Node.score);
        assume d#0 != null
             && d#0 != a#0
             && d#0 != b#0
             && d#0 != c#0
             && d#0 != d#0
             && d#0 != e#0
             && d#0 != f#0
           ==> read($Heap, d#0, _module.Node.rank)
             == read($PreCallHeap#0_0, d#0, _module.Node.rank);
        assume e#0 != null
             && e#0 != a#0
             && e#0 != b#0
             && e#0 != c#0
             && e#0 != d#0
             && e#0 != e#0
             && e#0 != f#0
           ==> read($Heap, e#0, _module.Node.val)
             == read($PreCallHeap#0_0, e#0, _module.Node.val);
        assume e#0 != null
             && e#0 != a#0
             && e#0 != b#0
             && e#0 != c#0
             && e#0 != d#0
             && e#0 != e#0
             && e#0 != f#0
           ==> read($Heap, e#0, _module.Node.tag)
             == read($PreCallHeap#0_0, e#0, _module.Node.tag);
        assume e#0 != null
             && e#0 != a#0
             && e#0 != b#0
             && e#0 != c#0
             && e#0 != d#0
             && e#0 != e#0
             && e#0 != f#0
           ==> read($Heap, e#0, _module.Node.score)
             == read($PreCallHeap#0_0, e#0, _module.Node.score);
        assume e#0 != null
             && e#0 != a#0
             && e#0 != b#0
             && e#0 != c#0
             && e#0 != d#0
             && e#0 != e#0
             && e#0 != f#0
           ==> read($Heap, e#0, _module.Node.rank)
             == read($PreCallHeap#0_0, e#0, _module.Node.rank);
        assume f#0 != null
             && f#0 != a#0
             && f#0 != b#0
             && f#0 != c#0
             && f#0 != d#0
             && f#0 != e#0
             && f#0 != f#0
           ==> read($Heap, f#0, _module.Node.val)
             == read($PreCallHeap#0_0, f#0, _module.Node.val);
        assume f#0 != null
             && f#0 != a#0
             && f#0 != b#0
             && f#0 != c#0
             && f#0 != d#0
             && f#0 != e#0
             && f#0 != f#0
           ==> read($Heap, f#0, _module.Node.tag)
             == read($PreCallHeap#0_0, f#0, _module.Node.tag);
        assume f#0 != null
             && f#0 != a#0
             && f#0 != b#0
             && f#0 != c#0
             && f#0 != d#0
             && f#0 != e#0
             && f#0 != f#0
           ==> read($Heap, f#0, _module.Node.score)
             == read($PreCallHeap#0_0, f#0, _module.Node.score);
        assume f#0 != null
             && f#0 != a#0
             && f#0 != b#0
             && f#0 != c#0
             && f#0 != d#0
             && f#0 != e#0
             && f#0 != f#0
           ==> read($Heap, f#0, _module.Node.rank)
             == read($PreCallHeap#0_0, f#0, _module.Node.rank);
        assume a##0_0 != null
             && a##0_0 != a#0
             && a##0_0 != b#0
             && a##0_0 != c#0
             && a##0_0 != d#0
             && a##0_0 != e#0
             && a##0_0 != f#0
           ==> read($Heap, a##0_0, _module.Node.val)
             == read($PreCallHeap#0_0, a##0_0, _module.Node.val);
        assume a##0_0 != null
             && a##0_0 != a#0
             && a##0_0 != b#0
             && a##0_0 != c#0
             && a##0_0 != d#0
             && a##0_0 != e#0
             && a##0_0 != f#0
           ==> read($Heap, a##0_0, _module.Node.tag)
             == read($PreCallHeap#0_0, a##0_0, _module.Node.tag);
        assume a##0_0 != null
             && a##0_0 != a#0
             && a##0_0 != b#0
             && a##0_0 != c#0
             && a##0_0 != d#0
             && a##0_0 != e#0
             && a##0_0 != f#0
           ==> read($Heap, a##0_0, _module.Node.score)
             == read($PreCallHeap#0_0, a##0_0, _module.Node.score);
        assume a##0_0 != null
             && a##0_0 != a#0
             && a##0_0 != b#0
             && a##0_0 != c#0
             && a##0_0 != d#0
             && a##0_0 != e#0
             && a##0_0 != f#0
           ==> read($Heap, a##0_0, _module.Node.rank)
             == read($PreCallHeap#0_0, a##0_0, _module.Node.rank);
        assume b##0_0 != null
             && b##0_0 != a#0
             && b##0_0 != b#0
             && b##0_0 != c#0
             && b##0_0 != d#0
             && b##0_0 != e#0
             && b##0_0 != f#0
           ==> read($Heap, b##0_0, _module.Node.val)
             == read($PreCallHeap#0_0, b##0_0, _module.Node.val);
        assume b##0_0 != null
             && b##0_0 != a#0
             && b##0_0 != b#0
             && b##0_0 != c#0
             && b##0_0 != d#0
             && b##0_0 != e#0
             && b##0_0 != f#0
           ==> read($Heap, b##0_0, _module.Node.tag)
             == read($PreCallHeap#0_0, b##0_0, _module.Node.tag);
        assume b##0_0 != null
             && b##0_0 != a#0
             && b##0_0 != b#0
             && b##0_0 != c#0
             && b##0_0 != d#0
             && b##0_0 != e#0
             && b##0_0 != f#0
           ==> read($Heap, b##0_0, _module.Node.score)
             == read($PreCallHeap#0_0, b##0_0, _module.Node.score);
        assume b##0_0 != null
             && b##0_0 != a#0
             && b##0_0 != b#0
             && b##0_0 != c#0
             && b##0_0 != d#0
             && b##0_0 != e#0
             && b##0_0 != f#0
           ==> read($Heap, b##0_0, _module.Node.rank)
             == read($PreCallHeap#0_0, b##0_0, _module.Node.rank);
        assume c##0_0 != null
             && c##0_0 != a#0
             && c##0_0 != b#0
             && c##0_0 != c#0
             && c##0_0 != d#0
             && c##0_0 != e#0
             && c##0_0 != f#0
           ==> read($Heap, c##0_0, _module.Node.val)
             == read($PreCallHeap#0_0, c##0_0, _module.Node.val);
        assume c##0_0 != null
             && c##0_0 != a#0
             && c##0_0 != b#0
             && c##0_0 != c#0
             && c##0_0 != d#0
             && c##0_0 != e#0
             && c##0_0 != f#0
           ==> read($Heap, c##0_0, _module.Node.tag)
             == read($PreCallHeap#0_0, c##0_0, _module.Node.tag);
        assume c##0_0 != null
             && c##0_0 != a#0
             && c##0_0 != b#0
             && c##0_0 != c#0
             && c##0_0 != d#0
             && c##0_0 != e#0
             && c##0_0 != f#0
           ==> read($Heap, c##0_0, _module.Node.score)
             == read($PreCallHeap#0_0, c##0_0, _module.Node.score);
        assume c##0_0 != null
             && c##0_0 != a#0
             && c##0_0 != b#0
             && c##0_0 != c#0
             && c##0_0 != d#0
             && c##0_0 != e#0
             && c##0_0 != f#0
           ==> read($Heap, c##0_0, _module.Node.rank)
             == read($PreCallHeap#0_0, c##0_0, _module.Node.rank);
        assume d##0_0 != null
             && d##0_0 != a#0
             && d##0_0 != b#0
             && d##0_0 != c#0
             && d##0_0 != d#0
             && d##0_0 != e#0
             && d##0_0 != f#0
           ==> read($Heap, d##0_0, _module.Node.val)
             == read($PreCallHeap#0_0, d##0_0, _module.Node.val);
        assume d##0_0 != null
             && d##0_0 != a#0
             && d##0_0 != b#0
             && d##0_0 != c#0
             && d##0_0 != d#0
             && d##0_0 != e#0
             && d##0_0 != f#0
           ==> read($Heap, d##0_0, _module.Node.tag)
             == read($PreCallHeap#0_0, d##0_0, _module.Node.tag);
        assume d##0_0 != null
             && d##0_0 != a#0
             && d##0_0 != b#0
             && d##0_0 != c#0
             && d##0_0 != d#0
             && d##0_0 != e#0
             && d##0_0 != f#0
           ==> read($Heap, d##0_0, _module.Node.score)
             == read($PreCallHeap#0_0, d##0_0, _module.Node.score);
        assume d##0_0 != null
             && d##0_0 != a#0
             && d##0_0 != b#0
             && d##0_0 != c#0
             && d##0_0 != d#0
             && d##0_0 != e#0
             && d##0_0 != f#0
           ==> read($Heap, d##0_0, _module.Node.rank)
             == read($PreCallHeap#0_0, d##0_0, _module.Node.rank);
        assume e##0_0 != null
             && e##0_0 != a#0
             && e##0_0 != b#0
             && e##0_0 != c#0
             && e##0_0 != d#0
             && e##0_0 != e#0
             && e##0_0 != f#0
           ==> read($Heap, e##0_0, _module.Node.val)
             == read($PreCallHeap#0_0, e##0_0, _module.Node.val);
        assume e##0_0 != null
             && e##0_0 != a#0
             && e##0_0 != b#0
             && e##0_0 != c#0
             && e##0_0 != d#0
             && e##0_0 != e#0
             && e##0_0 != f#0
           ==> read($Heap, e##0_0, _module.Node.tag)
             == read($PreCallHeap#0_0, e##0_0, _module.Node.tag);
        assume e##0_0 != null
             && e##0_0 != a#0
             && e##0_0 != b#0
             && e##0_0 != c#0
             && e##0_0 != d#0
             && e##0_0 != e#0
             && e##0_0 != f#0
           ==> read($Heap, e##0_0, _module.Node.score)
             == read($PreCallHeap#0_0, e##0_0, _module.Node.score);
        assume e##0_0 != null
             && e##0_0 != a#0
             && e##0_0 != b#0
             && e##0_0 != c#0
             && e##0_0 != d#0
             && e##0_0 != e#0
             && e##0_0 != f#0
           ==> read($Heap, e##0_0, _module.Node.rank)
             == read($PreCallHeap#0_0, e##0_0, _module.Node.rank);
        assume f##0_0 != null
             && f##0_0 != a#0
             && f##0_0 != b#0
             && f##0_0 != c#0
             && f##0_0 != d#0
             && f##0_0 != e#0
             && f##0_0 != f#0
           ==> read($Heap, f##0_0, _module.Node.val)
             == read($PreCallHeap#0_0, f##0_0, _module.Node.val);
        assume f##0_0 != null
             && f##0_0 != a#0
             && f##0_0 != b#0
             && f##0_0 != c#0
             && f##0_0 != d#0
             && f##0_0 != e#0
             && f##0_0 != f#0
           ==> read($Heap, f##0_0, _module.Node.tag)
             == read($PreCallHeap#0_0, f##0_0, _module.Node.tag);
        assume f##0_0 != null
             && f##0_0 != a#0
             && f##0_0 != b#0
             && f##0_0 != c#0
             && f##0_0 != d#0
             && f##0_0 != e#0
             && f##0_0 != f#0
           ==> read($Heap, f##0_0, _module.Node.score)
             == read($PreCallHeap#0_0, f##0_0, _module.Node.score);
        assume f##0_0 != null
             && f##0_0 != a#0
             && f##0_0 != b#0
             && f##0_0 != c#0
             && f##0_0 != d#0
             && f##0_0 != e#0
             && f##0_0 != f#0
           ==> read($Heap, f##0_0, _module.Node.rank)
             == read($PreCallHeap#0_0, f##0_0, _module.Node.rank);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "Test/arith.dfy(143,32)"} true;
        // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(144,7)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "Test/arith.dfy(144,14)"} true;
        assume true;
        // ----- loop termination check ----- /Users/saline/development/projects/dafny/Test/arith.dfy(134,3)
        assert {:id "id1341"} 0 <= $decr$loop#00 || n#0 - i#0 == $decr$loop#00;
        assert {:id "id1342"} n#0 - i#0 < $decr$loop#00;
        assume true;
    }
}



procedure {:verboseName "BumpNQuad (well-formedness)"} CheckWellFormed$$_module.__default.BumpNQuad(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]), 
    n#0: int);
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "BumpNQuad (well-formedness)"} CheckWellFormed$$_module.__default.BumpNQuad(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref, n#0: int)
{

    // AddMethodImpl: BumpNQuad, CheckWellFormed$$_module.__default.BumpNQuad
    assume {:captureState "Test/arith.dfy(152,7): initial state"} true;
    assume {:id "id1343"} n#0 >= LitInt(0);
    assume {:id "id1344"} a#0 != b#0;
    assume {:id "id1345"} a#0 != c#0;
    assume {:id "id1346"} a#0 != d#0;
    assume {:id "id1347"} a#0 != e#0;
    assume {:id "id1348"} a#0 != f#0;
    assume {:id "id1349"} b#0 != c#0;
    assume {:id "id1350"} b#0 != d#0;
    assume {:id "id1351"} b#0 != e#0;
    assume {:id "id1352"} b#0 != f#0;
    assume {:id "id1353"} c#0 != d#0;
    assume {:id "id1354"} c#0 != e#0;
    assume {:id "id1355"} c#0 != f#0;
    assume {:id "id1356"} d#0 != e#0;
    assume {:id "id1357"} d#0 != f#0;
    assume {:id "id1358"} e#0 != f#0;
    havoc $Heap;
    assume {:captureState "Test/arith.dfy(159,86): post-state"} true;
    assert {:id "id1359"} a#0 != null;
    assume true;
    assert {:id "id1360"} a#0 != null;
    assert {:id "id1361"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id1362"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
    assert {:id "id1363"} a#0 != null;
    assume true;
    assert {:id "id1364"} a#0 != null;
    assert {:id "id1365"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id1366"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id1367"} a#0 != null;
    assume true;
    assert {:id "id1368"} a#0 != null;
    assert {:id "id1369"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id1370"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id1371"} a#0 != null;
    assume true;
    assert {:id "id1372"} a#0 != null;
    assert {:id "id1373"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id1374"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
    assert {:id "id1375"} b#0 != null;
    assume true;
    assert {:id "id1376"} b#0 != null;
    assert {:id "id1377"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id1378"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
    assert {:id "id1379"} b#0 != null;
    assume true;
    assert {:id "id1380"} b#0 != null;
    assert {:id "id1381"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id1382"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id1383"} b#0 != null;
    assume true;
    assert {:id "id1384"} b#0 != null;
    assert {:id "id1385"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id1386"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id1387"} b#0 != null;
    assume true;
    assert {:id "id1388"} b#0 != null;
    assert {:id "id1389"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id1390"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
    assert {:id "id1391"} c#0 != null;
    assume true;
    assert {:id "id1392"} c#0 != null;
    assert {:id "id1393"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id1394"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
    assert {:id "id1395"} c#0 != null;
    assume true;
    assert {:id "id1396"} c#0 != null;
    assert {:id "id1397"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id1398"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id1399"} c#0 != null;
    assume true;
    assert {:id "id1400"} c#0 != null;
    assert {:id "id1401"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id1402"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id1403"} c#0 != null;
    assume true;
    assert {:id "id1404"} c#0 != null;
    assert {:id "id1405"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id1406"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
    assert {:id "id1407"} d#0 != null;
    assume true;
    assert {:id "id1408"} d#0 != null;
    assert {:id "id1409"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id1410"} $Unbox(read($Heap, d#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
    assert {:id "id1411"} d#0 != null;
    assume true;
    assert {:id "id1412"} d#0 != null;
    assert {:id "id1413"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id1414"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
    assert {:id "id1415"} d#0 != null;
    assume true;
    assert {:id "id1416"} d#0 != null;
    assert {:id "id1417"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id1418"} $Unbox(read($Heap, d#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
    assert {:id "id1419"} d#0 != null;
    assume true;
    assert {:id "id1420"} d#0 != null;
    assert {:id "id1421"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id1422"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
    assert {:id "id1423"} e#0 != null;
    assume true;
    assert {:id "id1424"} e#0 != null;
    assert {:id "id1425"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id1426"} $Unbox(read($Heap, e#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
    assert {:id "id1427"} e#0 != null;
    assume true;
    assert {:id "id1428"} e#0 != null;
    assert {:id "id1429"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id1430"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
    assert {:id "id1431"} e#0 != null;
    assume true;
    assert {:id "id1432"} e#0 != null;
    assert {:id "id1433"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id1434"} $Unbox(read($Heap, e#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
    assert {:id "id1435"} e#0 != null;
    assume true;
    assert {:id "id1436"} e#0 != null;
    assert {:id "id1437"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id1438"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
    assert {:id "id1439"} f#0 != null;
    assume true;
    assert {:id "id1440"} f#0 != null;
    assert {:id "id1441"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id1442"} $Unbox(read($Heap, f#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
    assert {:id "id1443"} f#0 != null;
    assume true;
    assert {:id "id1444"} f#0 != null;
    assert {:id "id1445"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id1446"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
    assert {:id "id1447"} f#0 != null;
    assume true;
    assert {:id "id1448"} f#0 != null;
    assert {:id "id1449"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id1450"} $Unbox(read($Heap, f#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
    assert {:id "id1451"} f#0 != null;
    assume true;
    assert {:id "id1452"} f#0 != null;
    assert {:id "id1453"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id1454"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
}



procedure {:verboseName "BumpNQuad (call)"} Call$$_module.__default.BumpNQuad(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]), 
    n#0: int);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id1455"} n#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id1456"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id1457"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1458"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1459"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1460"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1461"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1462"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1463"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1464"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1465"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1466"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1467"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1468"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1469"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1470"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id1471"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1472"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1473"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1474"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1475"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1476"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1477"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1478"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1479"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1480"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1481"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1482"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1483"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1484"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1485"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1486"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1487"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1488"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1489"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1490"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1491"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1492"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1493"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1494"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;



procedure {:verboseName "BumpNQuad (correctness)"} Impl$$_module.__default.BumpNQuad(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]), 
    n#0: int)
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id1495"} n#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id1496"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id1497"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1498"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1499"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1500"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1501"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1502"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1503"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1504"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1505"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1506"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1507"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1508"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1509"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1510"} e#0 != f#0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id1511"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1512"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1513"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1514"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1515"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1516"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1517"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1518"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1519"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1520"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1521"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1522"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1523"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1524"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1525"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1526"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1527"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1528"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1529"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1530"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1531"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(4), n#0);
  free ensures {:always_assume} true;
  ensures {:id "id1532"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1533"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1534"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "BumpNQuad (correctness)"} Impl$$_module.__default.BumpNQuad(a#0: ref, b#0: ref, c#0: ref, d#0: ref, e#0: ref, f#0: ref, n#0: int)
   returns ($_reverifyPost: bool)
{
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $PreLoopAlloc$loop#0: [ref]bool;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var a##0_0: ref;
  var b##0_0: ref;
  var c##0_0: ref;
  var d##0_0: ref;
  var e##0_0: ref;
  var f##0_0: ref;
  var $PreCallHeap#0_0: Heap;
  var $PreCallAlloc#0_0: [ref]bool;

    // AddMethodImpl: BumpNQuad, Impl$$_module.__default.BumpNQuad
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
    $PreLoopAlloc$loop#0 := $Alloc;
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
      invariant {:id "id1537"} $w$loop#0 ==> LitInt(0) <= i#0;
      invariant {:id "id1538"} $w$loop#0 ==> i#0 <= n#0;
      free invariant true;
      invariant {:id "id1552"} $w$loop#0
         ==> $Unbox(read($Heap, a#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(4), i#0);
      invariant {:id "id1553"} $w$loop#0
         ==> $Unbox(read($Heap, a#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
      invariant {:id "id1554"} $w$loop#0
         ==> $Unbox(read($Heap, a#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
      invariant {:id "id1555"} $w$loop#0
         ==> $Unbox(read($Heap, a#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1569"} $w$loop#0
         ==> $Unbox(read($Heap, b#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(4), i#0);
      invariant {:id "id1570"} $w$loop#0
         ==> $Unbox(read($Heap, b#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
      invariant {:id "id1571"} $w$loop#0
         ==> $Unbox(read($Heap, b#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
      invariant {:id "id1572"} $w$loop#0
         ==> $Unbox(read($Heap, b#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1586"} $w$loop#0
         ==> $Unbox(read($Heap, c#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(4), i#0);
      invariant {:id "id1587"} $w$loop#0
         ==> $Unbox(read($Heap, c#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
      invariant {:id "id1588"} $w$loop#0
         ==> $Unbox(read($Heap, c#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
      invariant {:id "id1589"} $w$loop#0
         ==> $Unbox(read($Heap, c#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1603"} $w$loop#0
         ==> $Unbox(read($Heap, d#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(4), i#0);
      invariant {:id "id1604"} $w$loop#0
         ==> $Unbox(read($Heap, d#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
      invariant {:id "id1605"} $w$loop#0
         ==> $Unbox(read($Heap, d#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
      invariant {:id "id1606"} $w$loop#0
         ==> $Unbox(read($Heap, d#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1620"} $w$loop#0
         ==> $Unbox(read($Heap, e#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(4), i#0);
      invariant {:id "id1621"} $w$loop#0
         ==> $Unbox(read($Heap, e#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
      invariant {:id "id1622"} $w$loop#0
         ==> $Unbox(read($Heap, e#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
      invariant {:id "id1623"} $w$loop#0
         ==> $Unbox(read($Heap, e#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
      free invariant true;
      invariant {:id "id1637"} $w$loop#0
         ==> $Unbox(read($Heap, f#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(4), i#0);
      invariant {:id "id1638"} $w$loop#0
         ==> $Unbox(read($Heap, f#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
      invariant {:id "id1639"} $w$loop#0
         ==> $Unbox(read($Heap, f#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
      invariant {:id "id1640"} $w$loop#0
         ==> $Unbox(read($Heap, f#0, _module.Node.rank)): int
           == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
      free invariant a#0 != null
           && a#0 != a#0
           && a#0 != b#0
           && a#0 != c#0
           && a#0 != d#0
           && a#0 != e#0
           && a#0 != f#0
         ==> read($PreLoopHeap$loop#0, a#0, _module.Node.val)
           == read($PreLoopHeap$loop#0, a#0, _module.Node.val);
      free invariant a#0 != null
           && a#0 != a#0
           && a#0 != b#0
           && a#0 != c#0
           && a#0 != d#0
           && a#0 != e#0
           && a#0 != f#0
         ==> read($PreLoopHeap$loop#0, a#0, _module.Node.tag)
           == read($PreLoopHeap$loop#0, a#0, _module.Node.tag);
      free invariant a#0 != null
           && a#0 != a#0
           && a#0 != b#0
           && a#0 != c#0
           && a#0 != d#0
           && a#0 != e#0
           && a#0 != f#0
         ==> read($PreLoopHeap$loop#0, a#0, _module.Node.score)
           == read($PreLoopHeap$loop#0, a#0, _module.Node.score);
      free invariant a#0 != null
           && a#0 != a#0
           && a#0 != b#0
           && a#0 != c#0
           && a#0 != d#0
           && a#0 != e#0
           && a#0 != f#0
         ==> read($PreLoopHeap$loop#0, a#0, _module.Node.rank)
           == read($PreLoopHeap$loop#0, a#0, _module.Node.rank);
      free invariant b#0 != null
           && b#0 != a#0
           && b#0 != b#0
           && b#0 != c#0
           && b#0 != d#0
           && b#0 != e#0
           && b#0 != f#0
         ==> read($PreLoopHeap$loop#0, b#0, _module.Node.val)
           == read($PreLoopHeap$loop#0, b#0, _module.Node.val);
      free invariant b#0 != null
           && b#0 != a#0
           && b#0 != b#0
           && b#0 != c#0
           && b#0 != d#0
           && b#0 != e#0
           && b#0 != f#0
         ==> read($PreLoopHeap$loop#0, b#0, _module.Node.tag)
           == read($PreLoopHeap$loop#0, b#0, _module.Node.tag);
      free invariant b#0 != null
           && b#0 != a#0
           && b#0 != b#0
           && b#0 != c#0
           && b#0 != d#0
           && b#0 != e#0
           && b#0 != f#0
         ==> read($PreLoopHeap$loop#0, b#0, _module.Node.score)
           == read($PreLoopHeap$loop#0, b#0, _module.Node.score);
      free invariant b#0 != null
           && b#0 != a#0
           && b#0 != b#0
           && b#0 != c#0
           && b#0 != d#0
           && b#0 != e#0
           && b#0 != f#0
         ==> read($PreLoopHeap$loop#0, b#0, _module.Node.rank)
           == read($PreLoopHeap$loop#0, b#0, _module.Node.rank);
      free invariant c#0 != null
           && c#0 != a#0
           && c#0 != b#0
           && c#0 != c#0
           && c#0 != d#0
           && c#0 != e#0
           && c#0 != f#0
         ==> read($PreLoopHeap$loop#0, c#0, _module.Node.val)
           == read($PreLoopHeap$loop#0, c#0, _module.Node.val);
      free invariant c#0 != null
           && c#0 != a#0
           && c#0 != b#0
           && c#0 != c#0
           && c#0 != d#0
           && c#0 != e#0
           && c#0 != f#0
         ==> read($PreLoopHeap$loop#0, c#0, _module.Node.tag)
           == read($PreLoopHeap$loop#0, c#0, _module.Node.tag);
      free invariant c#0 != null
           && c#0 != a#0
           && c#0 != b#0
           && c#0 != c#0
           && c#0 != d#0
           && c#0 != e#0
           && c#0 != f#0
         ==> read($PreLoopHeap$loop#0, c#0, _module.Node.score)
           == read($PreLoopHeap$loop#0, c#0, _module.Node.score);
      free invariant c#0 != null
           && c#0 != a#0
           && c#0 != b#0
           && c#0 != c#0
           && c#0 != d#0
           && c#0 != e#0
           && c#0 != f#0
         ==> read($PreLoopHeap$loop#0, c#0, _module.Node.rank)
           == read($PreLoopHeap$loop#0, c#0, _module.Node.rank);
      free invariant d#0 != null
           && d#0 != a#0
           && d#0 != b#0
           && d#0 != c#0
           && d#0 != d#0
           && d#0 != e#0
           && d#0 != f#0
         ==> read($PreLoopHeap$loop#0, d#0, _module.Node.val)
           == read($PreLoopHeap$loop#0, d#0, _module.Node.val);
      free invariant d#0 != null
           && d#0 != a#0
           && d#0 != b#0
           && d#0 != c#0
           && d#0 != d#0
           && d#0 != e#0
           && d#0 != f#0
         ==> read($PreLoopHeap$loop#0, d#0, _module.Node.tag)
           == read($PreLoopHeap$loop#0, d#0, _module.Node.tag);
      free invariant d#0 != null
           && d#0 != a#0
           && d#0 != b#0
           && d#0 != c#0
           && d#0 != d#0
           && d#0 != e#0
           && d#0 != f#0
         ==> read($PreLoopHeap$loop#0, d#0, _module.Node.score)
           == read($PreLoopHeap$loop#0, d#0, _module.Node.score);
      free invariant d#0 != null
           && d#0 != a#0
           && d#0 != b#0
           && d#0 != c#0
           && d#0 != d#0
           && d#0 != e#0
           && d#0 != f#0
         ==> read($PreLoopHeap$loop#0, d#0, _module.Node.rank)
           == read($PreLoopHeap$loop#0, d#0, _module.Node.rank);
      free invariant e#0 != null
           && e#0 != a#0
           && e#0 != b#0
           && e#0 != c#0
           && e#0 != d#0
           && e#0 != e#0
           && e#0 != f#0
         ==> read($PreLoopHeap$loop#0, e#0, _module.Node.val)
           == read($PreLoopHeap$loop#0, e#0, _module.Node.val);
      free invariant e#0 != null
           && e#0 != a#0
           && e#0 != b#0
           && e#0 != c#0
           && e#0 != d#0
           && e#0 != e#0
           && e#0 != f#0
         ==> read($PreLoopHeap$loop#0, e#0, _module.Node.tag)
           == read($PreLoopHeap$loop#0, e#0, _module.Node.tag);
      free invariant e#0 != null
           && e#0 != a#0
           && e#0 != b#0
           && e#0 != c#0
           && e#0 != d#0
           && e#0 != e#0
           && e#0 != f#0
         ==> read($PreLoopHeap$loop#0, e#0, _module.Node.score)
           == read($PreLoopHeap$loop#0, e#0, _module.Node.score);
      free invariant e#0 != null
           && e#0 != a#0
           && e#0 != b#0
           && e#0 != c#0
           && e#0 != d#0
           && e#0 != e#0
           && e#0 != f#0
         ==> read($PreLoopHeap$loop#0, e#0, _module.Node.rank)
           == read($PreLoopHeap$loop#0, e#0, _module.Node.rank);
      free invariant f#0 != null
           && f#0 != a#0
           && f#0 != b#0
           && f#0 != c#0
           && f#0 != d#0
           && f#0 != e#0
           && f#0 != f#0
         ==> read($PreLoopHeap$loop#0, f#0, _module.Node.val)
           == read($PreLoopHeap$loop#0, f#0, _module.Node.val);
      free invariant f#0 != null
           && f#0 != a#0
           && f#0 != b#0
           && f#0 != c#0
           && f#0 != d#0
           && f#0 != e#0
           && f#0 != f#0
         ==> read($PreLoopHeap$loop#0, f#0, _module.Node.tag)
           == read($PreLoopHeap$loop#0, f#0, _module.Node.tag);
      free invariant f#0 != null
           && f#0 != a#0
           && f#0 != b#0
           && f#0 != c#0
           && f#0 != d#0
           && f#0 != e#0
           && f#0 != f#0
         ==> read($PreLoopHeap$loop#0, f#0, _module.Node.score)
           == read($PreLoopHeap$loop#0, f#0, _module.Node.score);
      free invariant f#0 != null
           && f#0 != a#0
           && f#0 != b#0
           && f#0 != c#0
           && f#0 != d#0
           && f#0 != e#0
           && f#0 != f#0
         ==> read($PreLoopHeap$loop#0, f#0, _module.Node.rank)
           == read($PreLoopHeap$loop#0, f#0, _module.Node.rank);
      free invariant n#0 - i#0 <= $decr_init$loop#00;
    {
        assume {:captureState "Test/arith.dfy(167,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (LitInt(0) <= i#0)
            {
            }

            assume true;
            assume {:id "id1536"} LitInt(0) <= i#0 && i#0 <= n#0;
            assert {:id "id1539"} {:subsumption 0} a#0 != null;
            assume true;
            assert {:id "id1540"} {:subsumption 0} a#0 != null;
            assert {:id "id1541"} a#0 == null || old($Alloc)[a#0];
            assume true;
            if ($Unbox(read($Heap, a#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(4), i#0))
            {
                assert {:id "id1542"} {:subsumption 0} a#0 != null;
                assume true;
                assert {:id "id1543"} {:subsumption 0} a#0 != null;
                assert {:id "id1544"} a#0 == null || old($Alloc)[a#0];
                assume true;
            }

            if ($Unbox(read($Heap, a#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, a#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int)
            {
                assert {:id "id1545"} {:subsumption 0} a#0 != null;
                assume true;
                assert {:id "id1546"} {:subsumption 0} a#0 != null;
                assert {:id "id1547"} a#0 == null || old($Alloc)[a#0];
                assume true;
            }

            if ($Unbox(read($Heap, a#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, a#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int
               && $Unbox(read($Heap, a#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.score)): int)
            {
                assert {:id "id1548"} {:subsumption 0} a#0 != null;
                assume true;
                assert {:id "id1549"} {:subsumption 0} a#0 != null;
                assert {:id "id1550"} a#0 == null || old($Alloc)[a#0];
                assume true;
            }

            assume true;
            assume {:id "id1551"} $Unbox(read($Heap, a#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, a#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int
               && $Unbox(read($Heap, a#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.score)): int
               && $Unbox(read($Heap, a#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
            assert {:id "id1556"} {:subsumption 0} b#0 != null;
            assume true;
            assert {:id "id1557"} {:subsumption 0} b#0 != null;
            assert {:id "id1558"} b#0 == null || old($Alloc)[b#0];
            assume true;
            if ($Unbox(read($Heap, b#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(4), i#0))
            {
                assert {:id "id1559"} {:subsumption 0} b#0 != null;
                assume true;
                assert {:id "id1560"} {:subsumption 0} b#0 != null;
                assert {:id "id1561"} b#0 == null || old($Alloc)[b#0];
                assume true;
            }

            if ($Unbox(read($Heap, b#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, b#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int)
            {
                assert {:id "id1562"} {:subsumption 0} b#0 != null;
                assume true;
                assert {:id "id1563"} {:subsumption 0} b#0 != null;
                assert {:id "id1564"} b#0 == null || old($Alloc)[b#0];
                assume true;
            }

            if ($Unbox(read($Heap, b#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, b#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int
               && $Unbox(read($Heap, b#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.score)): int)
            {
                assert {:id "id1565"} {:subsumption 0} b#0 != null;
                assume true;
                assert {:id "id1566"} {:subsumption 0} b#0 != null;
                assert {:id "id1567"} b#0 == null || old($Alloc)[b#0];
                assume true;
            }

            assume true;
            assume {:id "id1568"} $Unbox(read($Heap, b#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, b#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int
               && $Unbox(read($Heap, b#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.score)): int
               && $Unbox(read($Heap, b#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
            assert {:id "id1573"} {:subsumption 0} c#0 != null;
            assume true;
            assert {:id "id1574"} {:subsumption 0} c#0 != null;
            assert {:id "id1575"} c#0 == null || old($Alloc)[c#0];
            assume true;
            if ($Unbox(read($Heap, c#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(4), i#0))
            {
                assert {:id "id1576"} {:subsumption 0} c#0 != null;
                assume true;
                assert {:id "id1577"} {:subsumption 0} c#0 != null;
                assert {:id "id1578"} c#0 == null || old($Alloc)[c#0];
                assume true;
            }

            if ($Unbox(read($Heap, c#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, c#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int)
            {
                assert {:id "id1579"} {:subsumption 0} c#0 != null;
                assume true;
                assert {:id "id1580"} {:subsumption 0} c#0 != null;
                assert {:id "id1581"} c#0 == null || old($Alloc)[c#0];
                assume true;
            }

            if ($Unbox(read($Heap, c#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, c#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int
               && $Unbox(read($Heap, c#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.score)): int)
            {
                assert {:id "id1582"} {:subsumption 0} c#0 != null;
                assume true;
                assert {:id "id1583"} {:subsumption 0} c#0 != null;
                assert {:id "id1584"} c#0 == null || old($Alloc)[c#0];
                assume true;
            }

            assume true;
            assume {:id "id1585"} $Unbox(read($Heap, c#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, c#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int
               && $Unbox(read($Heap, c#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.score)): int
               && $Unbox(read($Heap, c#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
            assert {:id "id1590"} {:subsumption 0} d#0 != null;
            assume true;
            assert {:id "id1591"} {:subsumption 0} d#0 != null;
            assert {:id "id1592"} d#0 == null || old($Alloc)[d#0];
            assume true;
            if ($Unbox(read($Heap, d#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(4), i#0))
            {
                assert {:id "id1593"} {:subsumption 0} d#0 != null;
                assume true;
                assert {:id "id1594"} {:subsumption 0} d#0 != null;
                assert {:id "id1595"} d#0 == null || old($Alloc)[d#0];
                assume true;
            }

            if ($Unbox(read($Heap, d#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, d#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int)
            {
                assert {:id "id1596"} {:subsumption 0} d#0 != null;
                assume true;
                assert {:id "id1597"} {:subsumption 0} d#0 != null;
                assert {:id "id1598"} d#0 == null || old($Alloc)[d#0];
                assume true;
            }

            if ($Unbox(read($Heap, d#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, d#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int
               && $Unbox(read($Heap, d#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.score)): int)
            {
                assert {:id "id1599"} {:subsumption 0} d#0 != null;
                assume true;
                assert {:id "id1600"} {:subsumption 0} d#0 != null;
                assert {:id "id1601"} d#0 == null || old($Alloc)[d#0];
                assume true;
            }

            assume true;
            assume {:id "id1602"} $Unbox(read($Heap, d#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, d#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int
               && $Unbox(read($Heap, d#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.score)): int
               && $Unbox(read($Heap, d#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
            assert {:id "id1607"} {:subsumption 0} e#0 != null;
            assume true;
            assert {:id "id1608"} {:subsumption 0} e#0 != null;
            assert {:id "id1609"} e#0 == null || old($Alloc)[e#0];
            assume true;
            if ($Unbox(read($Heap, e#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(4), i#0))
            {
                assert {:id "id1610"} {:subsumption 0} e#0 != null;
                assume true;
                assert {:id "id1611"} {:subsumption 0} e#0 != null;
                assert {:id "id1612"} e#0 == null || old($Alloc)[e#0];
                assume true;
            }

            if ($Unbox(read($Heap, e#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, e#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int)
            {
                assert {:id "id1613"} {:subsumption 0} e#0 != null;
                assume true;
                assert {:id "id1614"} {:subsumption 0} e#0 != null;
                assert {:id "id1615"} e#0 == null || old($Alloc)[e#0];
                assume true;
            }

            if ($Unbox(read($Heap, e#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, e#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int
               && $Unbox(read($Heap, e#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.score)): int)
            {
                assert {:id "id1616"} {:subsumption 0} e#0 != null;
                assume true;
                assert {:id "id1617"} {:subsumption 0} e#0 != null;
                assert {:id "id1618"} e#0 == null || old($Alloc)[e#0];
                assume true;
            }

            assume true;
            assume {:id "id1619"} $Unbox(read($Heap, e#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, e#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int
               && $Unbox(read($Heap, e#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.score)): int
               && $Unbox(read($Heap, e#0, _module.Node.rank)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
            assert {:id "id1624"} {:subsumption 0} f#0 != null;
            assume true;
            assert {:id "id1625"} {:subsumption 0} f#0 != null;
            assert {:id "id1626"} f#0 == null || old($Alloc)[f#0];
            assume true;
            if ($Unbox(read($Heap, f#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(4), i#0))
            {
                assert {:id "id1627"} {:subsumption 0} f#0 != null;
                assume true;
                assert {:id "id1628"} {:subsumption 0} f#0 != null;
                assert {:id "id1629"} f#0 == null || old($Alloc)[f#0];
                assume true;
            }

            if ($Unbox(read($Heap, f#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, f#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int)
            {
                assert {:id "id1630"} {:subsumption 0} f#0 != null;
                assume true;
                assert {:id "id1631"} {:subsumption 0} f#0 != null;
                assert {:id "id1632"} f#0 == null || old($Alloc)[f#0];
                assume true;
            }

            if ($Unbox(read($Heap, f#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + Mul(LitInt(4), i#0)
               && $Unbox(read($Heap, f#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int
               && $Unbox(read($Heap, f#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.score)): int)
            {
                assert {:id "id1633"} {:subsumption 0} f#0 != null;
                assume true;
                assert {:id "id1634"} {:subsumption 0} f#0 != null;
                assert {:id "id1635"} f#0 == null || old($Alloc)[f#0];
                assume true;
            }

            assume true;
            assume {:id "id1636"} $Unbox(read($Heap, f#0, _module.Node.val)): int
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
        $PreCallHeap#0_0 := $Heap;
        $PreCallAlloc#0_0 := $Alloc;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assert {:id "id1641"} a##0_0 == a#0
           || a##0_0 == b#0
           || a##0_0 == c#0
           || a##0_0 == d#0
           || a##0_0 == e#0
           || a##0_0 == f#0
           || !old($Alloc)[a##0_0];
        assert {:id "id1642"} b##0_0 == a#0
           || b##0_0 == b#0
           || b##0_0 == c#0
           || b##0_0 == d#0
           || b##0_0 == e#0
           || b##0_0 == f#0
           || !old($Alloc)[b##0_0];
        assert {:id "id1643"} c##0_0 == a#0
           || c##0_0 == b#0
           || c##0_0 == c#0
           || c##0_0 == d#0
           || c##0_0 == e#0
           || c##0_0 == f#0
           || !old($Alloc)[c##0_0];
        assert {:id "id1644"} d##0_0 == a#0
           || d##0_0 == b#0
           || d##0_0 == c#0
           || d##0_0 == d#0
           || d##0_0 == e#0
           || d##0_0 == f#0
           || !old($Alloc)[d##0_0];
        assert {:id "id1645"} e##0_0 == a#0
           || e##0_0 == b#0
           || e##0_0 == c#0
           || e##0_0 == d#0
           || e##0_0 == e#0
           || e##0_0 == f#0
           || !old($Alloc)[e##0_0];
        assert {:id "id1646"} f##0_0 == a#0
           || f##0_0 == b#0
           || f##0_0 == c#0
           || f##0_0 == d#0
           || f##0_0 == e#0
           || f##0_0 == f#0
           || !old($Alloc)[f##0_0];
        call {:id "id1647"} Call$$_module.__default.QuadBump(a##0_0, b##0_0, c##0_0, d##0_0, e##0_0, f##0_0);
        // qf-call-frame QuadBump: supports=12 reads=48 modified=6
        assume a#0 != null
             && a#0 != a#0
             && a#0 != b#0
             && a#0 != c#0
             && a#0 != d#0
             && a#0 != e#0
             && a#0 != f#0
           ==> read($Heap, a#0, _module.Node.val)
             == read($PreCallHeap#0_0, a#0, _module.Node.val);
        assume a#0 != null
             && a#0 != a#0
             && a#0 != b#0
             && a#0 != c#0
             && a#0 != d#0
             && a#0 != e#0
             && a#0 != f#0
           ==> read($Heap, a#0, _module.Node.tag)
             == read($PreCallHeap#0_0, a#0, _module.Node.tag);
        assume a#0 != null
             && a#0 != a#0
             && a#0 != b#0
             && a#0 != c#0
             && a#0 != d#0
             && a#0 != e#0
             && a#0 != f#0
           ==> read($Heap, a#0, _module.Node.score)
             == read($PreCallHeap#0_0, a#0, _module.Node.score);
        assume a#0 != null
             && a#0 != a#0
             && a#0 != b#0
             && a#0 != c#0
             && a#0 != d#0
             && a#0 != e#0
             && a#0 != f#0
           ==> read($Heap, a#0, _module.Node.rank)
             == read($PreCallHeap#0_0, a#0, _module.Node.rank);
        assume b#0 != null
             && b#0 != a#0
             && b#0 != b#0
             && b#0 != c#0
             && b#0 != d#0
             && b#0 != e#0
             && b#0 != f#0
           ==> read($Heap, b#0, _module.Node.val)
             == read($PreCallHeap#0_0, b#0, _module.Node.val);
        assume b#0 != null
             && b#0 != a#0
             && b#0 != b#0
             && b#0 != c#0
             && b#0 != d#0
             && b#0 != e#0
             && b#0 != f#0
           ==> read($Heap, b#0, _module.Node.tag)
             == read($PreCallHeap#0_0, b#0, _module.Node.tag);
        assume b#0 != null
             && b#0 != a#0
             && b#0 != b#0
             && b#0 != c#0
             && b#0 != d#0
             && b#0 != e#0
             && b#0 != f#0
           ==> read($Heap, b#0, _module.Node.score)
             == read($PreCallHeap#0_0, b#0, _module.Node.score);
        assume b#0 != null
             && b#0 != a#0
             && b#0 != b#0
             && b#0 != c#0
             && b#0 != d#0
             && b#0 != e#0
             && b#0 != f#0
           ==> read($Heap, b#0, _module.Node.rank)
             == read($PreCallHeap#0_0, b#0, _module.Node.rank);
        assume c#0 != null
             && c#0 != a#0
             && c#0 != b#0
             && c#0 != c#0
             && c#0 != d#0
             && c#0 != e#0
             && c#0 != f#0
           ==> read($Heap, c#0, _module.Node.val)
             == read($PreCallHeap#0_0, c#0, _module.Node.val);
        assume c#0 != null
             && c#0 != a#0
             && c#0 != b#0
             && c#0 != c#0
             && c#0 != d#0
             && c#0 != e#0
             && c#0 != f#0
           ==> read($Heap, c#0, _module.Node.tag)
             == read($PreCallHeap#0_0, c#0, _module.Node.tag);
        assume c#0 != null
             && c#0 != a#0
             && c#0 != b#0
             && c#0 != c#0
             && c#0 != d#0
             && c#0 != e#0
             && c#0 != f#0
           ==> read($Heap, c#0, _module.Node.score)
             == read($PreCallHeap#0_0, c#0, _module.Node.score);
        assume c#0 != null
             && c#0 != a#0
             && c#0 != b#0
             && c#0 != c#0
             && c#0 != d#0
             && c#0 != e#0
             && c#0 != f#0
           ==> read($Heap, c#0, _module.Node.rank)
             == read($PreCallHeap#0_0, c#0, _module.Node.rank);
        assume d#0 != null
             && d#0 != a#0
             && d#0 != b#0
             && d#0 != c#0
             && d#0 != d#0
             && d#0 != e#0
             && d#0 != f#0
           ==> read($Heap, d#0, _module.Node.val)
             == read($PreCallHeap#0_0, d#0, _module.Node.val);
        assume d#0 != null
             && d#0 != a#0
             && d#0 != b#0
             && d#0 != c#0
             && d#0 != d#0
             && d#0 != e#0
             && d#0 != f#0
           ==> read($Heap, d#0, _module.Node.tag)
             == read($PreCallHeap#0_0, d#0, _module.Node.tag);
        assume d#0 != null
             && d#0 != a#0
             && d#0 != b#0
             && d#0 != c#0
             && d#0 != d#0
             && d#0 != e#0
             && d#0 != f#0
           ==> read($Heap, d#0, _module.Node.score)
             == read($PreCallHeap#0_0, d#0, _module.Node.score);
        assume d#0 != null
             && d#0 != a#0
             && d#0 != b#0
             && d#0 != c#0
             && d#0 != d#0
             && d#0 != e#0
             && d#0 != f#0
           ==> read($Heap, d#0, _module.Node.rank)
             == read($PreCallHeap#0_0, d#0, _module.Node.rank);
        assume e#0 != null
             && e#0 != a#0
             && e#0 != b#0
             && e#0 != c#0
             && e#0 != d#0
             && e#0 != e#0
             && e#0 != f#0
           ==> read($Heap, e#0, _module.Node.val)
             == read($PreCallHeap#0_0, e#0, _module.Node.val);
        assume e#0 != null
             && e#0 != a#0
             && e#0 != b#0
             && e#0 != c#0
             && e#0 != d#0
             && e#0 != e#0
             && e#0 != f#0
           ==> read($Heap, e#0, _module.Node.tag)
             == read($PreCallHeap#0_0, e#0, _module.Node.tag);
        assume e#0 != null
             && e#0 != a#0
             && e#0 != b#0
             && e#0 != c#0
             && e#0 != d#0
             && e#0 != e#0
             && e#0 != f#0
           ==> read($Heap, e#0, _module.Node.score)
             == read($PreCallHeap#0_0, e#0, _module.Node.score);
        assume e#0 != null
             && e#0 != a#0
             && e#0 != b#0
             && e#0 != c#0
             && e#0 != d#0
             && e#0 != e#0
             && e#0 != f#0
           ==> read($Heap, e#0, _module.Node.rank)
             == read($PreCallHeap#0_0, e#0, _module.Node.rank);
        assume f#0 != null
             && f#0 != a#0
             && f#0 != b#0
             && f#0 != c#0
             && f#0 != d#0
             && f#0 != e#0
             && f#0 != f#0
           ==> read($Heap, f#0, _module.Node.val)
             == read($PreCallHeap#0_0, f#0, _module.Node.val);
        assume f#0 != null
             && f#0 != a#0
             && f#0 != b#0
             && f#0 != c#0
             && f#0 != d#0
             && f#0 != e#0
             && f#0 != f#0
           ==> read($Heap, f#0, _module.Node.tag)
             == read($PreCallHeap#0_0, f#0, _module.Node.tag);
        assume f#0 != null
             && f#0 != a#0
             && f#0 != b#0
             && f#0 != c#0
             && f#0 != d#0
             && f#0 != e#0
             && f#0 != f#0
           ==> read($Heap, f#0, _module.Node.score)
             == read($PreCallHeap#0_0, f#0, _module.Node.score);
        assume f#0 != null
             && f#0 != a#0
             && f#0 != b#0
             && f#0 != c#0
             && f#0 != d#0
             && f#0 != e#0
             && f#0 != f#0
           ==> read($Heap, f#0, _module.Node.rank)
             == read($PreCallHeap#0_0, f#0, _module.Node.rank);
        assume a##0_0 != null
             && a##0_0 != a#0
             && a##0_0 != b#0
             && a##0_0 != c#0
             && a##0_0 != d#0
             && a##0_0 != e#0
             && a##0_0 != f#0
           ==> read($Heap, a##0_0, _module.Node.val)
             == read($PreCallHeap#0_0, a##0_0, _module.Node.val);
        assume a##0_0 != null
             && a##0_0 != a#0
             && a##0_0 != b#0
             && a##0_0 != c#0
             && a##0_0 != d#0
             && a##0_0 != e#0
             && a##0_0 != f#0
           ==> read($Heap, a##0_0, _module.Node.tag)
             == read($PreCallHeap#0_0, a##0_0, _module.Node.tag);
        assume a##0_0 != null
             && a##0_0 != a#0
             && a##0_0 != b#0
             && a##0_0 != c#0
             && a##0_0 != d#0
             && a##0_0 != e#0
             && a##0_0 != f#0
           ==> read($Heap, a##0_0, _module.Node.score)
             == read($PreCallHeap#0_0, a##0_0, _module.Node.score);
        assume a##0_0 != null
             && a##0_0 != a#0
             && a##0_0 != b#0
             && a##0_0 != c#0
             && a##0_0 != d#0
             && a##0_0 != e#0
             && a##0_0 != f#0
           ==> read($Heap, a##0_0, _module.Node.rank)
             == read($PreCallHeap#0_0, a##0_0, _module.Node.rank);
        assume b##0_0 != null
             && b##0_0 != a#0
             && b##0_0 != b#0
             && b##0_0 != c#0
             && b##0_0 != d#0
             && b##0_0 != e#0
             && b##0_0 != f#0
           ==> read($Heap, b##0_0, _module.Node.val)
             == read($PreCallHeap#0_0, b##0_0, _module.Node.val);
        assume b##0_0 != null
             && b##0_0 != a#0
             && b##0_0 != b#0
             && b##0_0 != c#0
             && b##0_0 != d#0
             && b##0_0 != e#0
             && b##0_0 != f#0
           ==> read($Heap, b##0_0, _module.Node.tag)
             == read($PreCallHeap#0_0, b##0_0, _module.Node.tag);
        assume b##0_0 != null
             && b##0_0 != a#0
             && b##0_0 != b#0
             && b##0_0 != c#0
             && b##0_0 != d#0
             && b##0_0 != e#0
             && b##0_0 != f#0
           ==> read($Heap, b##0_0, _module.Node.score)
             == read($PreCallHeap#0_0, b##0_0, _module.Node.score);
        assume b##0_0 != null
             && b##0_0 != a#0
             && b##0_0 != b#0
             && b##0_0 != c#0
             && b##0_0 != d#0
             && b##0_0 != e#0
             && b##0_0 != f#0
           ==> read($Heap, b##0_0, _module.Node.rank)
             == read($PreCallHeap#0_0, b##0_0, _module.Node.rank);
        assume c##0_0 != null
             && c##0_0 != a#0
             && c##0_0 != b#0
             && c##0_0 != c#0
             && c##0_0 != d#0
             && c##0_0 != e#0
             && c##0_0 != f#0
           ==> read($Heap, c##0_0, _module.Node.val)
             == read($PreCallHeap#0_0, c##0_0, _module.Node.val);
        assume c##0_0 != null
             && c##0_0 != a#0
             && c##0_0 != b#0
             && c##0_0 != c#0
             && c##0_0 != d#0
             && c##0_0 != e#0
             && c##0_0 != f#0
           ==> read($Heap, c##0_0, _module.Node.tag)
             == read($PreCallHeap#0_0, c##0_0, _module.Node.tag);
        assume c##0_0 != null
             && c##0_0 != a#0
             && c##0_0 != b#0
             && c##0_0 != c#0
             && c##0_0 != d#0
             && c##0_0 != e#0
             && c##0_0 != f#0
           ==> read($Heap, c##0_0, _module.Node.score)
             == read($PreCallHeap#0_0, c##0_0, _module.Node.score);
        assume c##0_0 != null
             && c##0_0 != a#0
             && c##0_0 != b#0
             && c##0_0 != c#0
             && c##0_0 != d#0
             && c##0_0 != e#0
             && c##0_0 != f#0
           ==> read($Heap, c##0_0, _module.Node.rank)
             == read($PreCallHeap#0_0, c##0_0, _module.Node.rank);
        assume d##0_0 != null
             && d##0_0 != a#0
             && d##0_0 != b#0
             && d##0_0 != c#0
             && d##0_0 != d#0
             && d##0_0 != e#0
             && d##0_0 != f#0
           ==> read($Heap, d##0_0, _module.Node.val)
             == read($PreCallHeap#0_0, d##0_0, _module.Node.val);
        assume d##0_0 != null
             && d##0_0 != a#0
             && d##0_0 != b#0
             && d##0_0 != c#0
             && d##0_0 != d#0
             && d##0_0 != e#0
             && d##0_0 != f#0
           ==> read($Heap, d##0_0, _module.Node.tag)
             == read($PreCallHeap#0_0, d##0_0, _module.Node.tag);
        assume d##0_0 != null
             && d##0_0 != a#0
             && d##0_0 != b#0
             && d##0_0 != c#0
             && d##0_0 != d#0
             && d##0_0 != e#0
             && d##0_0 != f#0
           ==> read($Heap, d##0_0, _module.Node.score)
             == read($PreCallHeap#0_0, d##0_0, _module.Node.score);
        assume d##0_0 != null
             && d##0_0 != a#0
             && d##0_0 != b#0
             && d##0_0 != c#0
             && d##0_0 != d#0
             && d##0_0 != e#0
             && d##0_0 != f#0
           ==> read($Heap, d##0_0, _module.Node.rank)
             == read($PreCallHeap#0_0, d##0_0, _module.Node.rank);
        assume e##0_0 != null
             && e##0_0 != a#0
             && e##0_0 != b#0
             && e##0_0 != c#0
             && e##0_0 != d#0
             && e##0_0 != e#0
             && e##0_0 != f#0
           ==> read($Heap, e##0_0, _module.Node.val)
             == read($PreCallHeap#0_0, e##0_0, _module.Node.val);
        assume e##0_0 != null
             && e##0_0 != a#0
             && e##0_0 != b#0
             && e##0_0 != c#0
             && e##0_0 != d#0
             && e##0_0 != e#0
             && e##0_0 != f#0
           ==> read($Heap, e##0_0, _module.Node.tag)
             == read($PreCallHeap#0_0, e##0_0, _module.Node.tag);
        assume e##0_0 != null
             && e##0_0 != a#0
             && e##0_0 != b#0
             && e##0_0 != c#0
             && e##0_0 != d#0
             && e##0_0 != e#0
             && e##0_0 != f#0
           ==> read($Heap, e##0_0, _module.Node.score)
             == read($PreCallHeap#0_0, e##0_0, _module.Node.score);
        assume e##0_0 != null
             && e##0_0 != a#0
             && e##0_0 != b#0
             && e##0_0 != c#0
             && e##0_0 != d#0
             && e##0_0 != e#0
             && e##0_0 != f#0
           ==> read($Heap, e##0_0, _module.Node.rank)
             == read($PreCallHeap#0_0, e##0_0, _module.Node.rank);
        assume f##0_0 != null
             && f##0_0 != a#0
             && f##0_0 != b#0
             && f##0_0 != c#0
             && f##0_0 != d#0
             && f##0_0 != e#0
             && f##0_0 != f#0
           ==> read($Heap, f##0_0, _module.Node.val)
             == read($PreCallHeap#0_0, f##0_0, _module.Node.val);
        assume f##0_0 != null
             && f##0_0 != a#0
             && f##0_0 != b#0
             && f##0_0 != c#0
             && f##0_0 != d#0
             && f##0_0 != e#0
             && f##0_0 != f#0
           ==> read($Heap, f##0_0, _module.Node.tag)
             == read($PreCallHeap#0_0, f##0_0, _module.Node.tag);
        assume f##0_0 != null
             && f##0_0 != a#0
             && f##0_0 != b#0
             && f##0_0 != c#0
             && f##0_0 != d#0
             && f##0_0 != e#0
             && f##0_0 != f#0
           ==> read($Heap, f##0_0, _module.Node.score)
             == read($PreCallHeap#0_0, f##0_0, _module.Node.score);
        assume f##0_0 != null
             && f##0_0 != a#0
             && f##0_0 != b#0
             && f##0_0 != c#0
             && f##0_0 != d#0
             && f##0_0 != e#0
             && f##0_0 != f#0
           ==> read($Heap, f##0_0, _module.Node.rank)
             == read($PreCallHeap#0_0, f##0_0, _module.Node.rank);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "Test/arith.dfy(176,30)"} true;
        // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(177,7)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "Test/arith.dfy(177,14)"} true;
        assume true;
        // ----- loop termination check ----- /Users/saline/development/projects/dafny/Test/arith.dfy(167,3)
        assert {:id "id1649"} 0 <= $decr$loop#00 || n#0 - i#0 == $decr$loop#00;
        assert {:id "id1650"} n#0 - i#0 < $decr$loop#00;
        assume true;
    }
}



procedure {:verboseName "StressTest (well-formedness)"} CheckWellFormed$$_module.__default.StressTest(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]), 
    p#0: ref where $Is(p#0, Tclass._module.Node()) && (p#0 == null || $Alloc[p#0]), 
    q#0: ref where $Is(q#0, Tclass._module.Node()) && (q#0 == null || $Alloc[q#0]), 
    r#0: ref where $Is(r#0, Tclass._module.Node()) && (r#0 == null || $Alloc[r#0]), 
    s#0: ref where $Is(s#0, Tclass._module.Node()) && (s#0 == null || $Alloc[s#0]), 
    t#0: ref where $Is(t#0, Tclass._module.Node()) && (t#0 == null || $Alloc[t#0]), 
    u#0: ref where $Is(u#0, Tclass._module.Node()) && (u#0 == null || $Alloc[u#0]), 
    m#0: int, 
    n#0: int);
  modifies $Heap, $Alloc;



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

    // AddMethodImpl: StressTest, CheckWellFormed$$_module.__default.StressTest
    assume {:captureState "Test/arith.dfy(190,7): initial state"} true;
    assume {:id "id1651"} m#0 >= LitInt(0);
    assume {:id "id1652"} n#0 >= LitInt(0);
    assume {:id "id1653"} a#0 != b#0;
    assume {:id "id1654"} a#0 != c#0;
    assume {:id "id1655"} a#0 != d#0;
    assume {:id "id1656"} a#0 != e#0;
    assume {:id "id1657"} a#0 != f#0;
    assume {:id "id1658"} b#0 != c#0;
    assume {:id "id1659"} b#0 != d#0;
    assume {:id "id1660"} b#0 != e#0;
    assume {:id "id1661"} b#0 != f#0;
    assume {:id "id1662"} c#0 != d#0;
    assume {:id "id1663"} c#0 != e#0;
    assume {:id "id1664"} c#0 != f#0;
    assume {:id "id1665"} d#0 != e#0;
    assume {:id "id1666"} d#0 != f#0;
    assume {:id "id1667"} e#0 != f#0;
    assume {:id "id1668"} p#0 != q#0;
    assume {:id "id1669"} p#0 != r#0;
    assume {:id "id1670"} p#0 != s#0;
    assume {:id "id1671"} p#0 != t#0;
    assume {:id "id1672"} p#0 != u#0;
    assume {:id "id1673"} q#0 != r#0;
    assume {:id "id1674"} q#0 != s#0;
    assume {:id "id1675"} q#0 != t#0;
    assume {:id "id1676"} q#0 != u#0;
    assume {:id "id1677"} r#0 != s#0;
    assume {:id "id1678"} r#0 != t#0;
    assume {:id "id1679"} r#0 != u#0;
    assume {:id "id1680"} s#0 != t#0;
    assume {:id "id1681"} s#0 != u#0;
    assume {:id "id1682"} t#0 != u#0;
    assume {:id "id1683"} a#0 != p#0;
    assume {:id "id1684"} a#0 != q#0;
    assume {:id "id1685"} a#0 != r#0;
    assume {:id "id1686"} a#0 != s#0;
    assume {:id "id1687"} a#0 != t#0;
    assume {:id "id1688"} a#0 != u#0;
    assume {:id "id1689"} b#0 != p#0;
    assume {:id "id1690"} b#0 != q#0;
    assume {:id "id1691"} b#0 != r#0;
    assume {:id "id1692"} b#0 != s#0;
    assume {:id "id1693"} b#0 != t#0;
    assume {:id "id1694"} b#0 != u#0;
    assume {:id "id1695"} c#0 != p#0;
    assume {:id "id1696"} c#0 != q#0;
    assume {:id "id1697"} c#0 != r#0;
    assume {:id "id1698"} c#0 != s#0;
    assume {:id "id1699"} c#0 != t#0;
    assume {:id "id1700"} c#0 != u#0;
    assume {:id "id1701"} d#0 != p#0;
    assume {:id "id1702"} d#0 != q#0;
    assume {:id "id1703"} d#0 != r#0;
    assume {:id "id1704"} d#0 != s#0;
    assume {:id "id1705"} d#0 != t#0;
    assume {:id "id1706"} d#0 != u#0;
    assume {:id "id1707"} e#0 != p#0;
    assume {:id "id1708"} e#0 != q#0;
    assume {:id "id1709"} e#0 != r#0;
    assume {:id "id1710"} e#0 != s#0;
    assume {:id "id1711"} e#0 != t#0;
    assume {:id "id1712"} e#0 != u#0;
    assume {:id "id1713"} f#0 != p#0;
    assume {:id "id1714"} f#0 != q#0;
    assume {:id "id1715"} f#0 != r#0;
    assume {:id "id1716"} f#0 != s#0;
    assume {:id "id1717"} f#0 != t#0;
    assume {:id "id1718"} f#0 != u#0;
    havoc $Heap;
    assume {:captureState "Test/arith.dfy(214,96): post-state"} true;
    assert {:id "id1719"} a#0 != null;
    assume true;
    assert {:id "id1720"} a#0 != null;
    assert {:id "id1721"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id1722"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int
         + Mul(LitInt(2), m#0)
         + Mul(LitInt(4), n#0)
         + 9;
    assert {:id "id1723"} a#0 != null;
    assume true;
    assert {:id "id1724"} a#0 != null;
    assert {:id "id1725"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id1726"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id1727"} a#0 != null;
    assume true;
    assert {:id "id1728"} a#0 != null;
    assert {:id "id1729"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id1730"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id1731"} a#0 != null;
    assume true;
    assert {:id "id1732"} a#0 != null;
    assert {:id "id1733"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id1734"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
    assert {:id "id1735"} b#0 != null;
    assume true;
    assert {:id "id1736"} b#0 != null;
    assert {:id "id1737"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id1738"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int
         + Mul(LitInt(2), m#0)
         + Mul(LitInt(4), n#0)
         + 9;
    assert {:id "id1739"} b#0 != null;
    assume true;
    assert {:id "id1740"} b#0 != null;
    assert {:id "id1741"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id1742"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id1743"} b#0 != null;
    assume true;
    assert {:id "id1744"} b#0 != null;
    assert {:id "id1745"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id1746"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id1747"} b#0 != null;
    assume true;
    assert {:id "id1748"} b#0 != null;
    assert {:id "id1749"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id1750"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
    assert {:id "id1751"} c#0 != null;
    assume true;
    assert {:id "id1752"} c#0 != null;
    assert {:id "id1753"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id1754"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int
         + Mul(LitInt(2), m#0)
         + Mul(LitInt(4), n#0)
         + 9;
    assert {:id "id1755"} c#0 != null;
    assume true;
    assert {:id "id1756"} c#0 != null;
    assert {:id "id1757"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id1758"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id1759"} c#0 != null;
    assume true;
    assert {:id "id1760"} c#0 != null;
    assert {:id "id1761"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id1762"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id1763"} c#0 != null;
    assume true;
    assert {:id "id1764"} c#0 != null;
    assert {:id "id1765"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id1766"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
    assert {:id "id1767"} d#0 != null;
    assume true;
    assert {:id "id1768"} d#0 != null;
    assert {:id "id1769"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id1770"} $Unbox(read($Heap, d#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.val)): int
         + Mul(LitInt(2), m#0)
         + Mul(LitInt(4), n#0)
         + 8;
    assert {:id "id1771"} d#0 != null;
    assume true;
    assert {:id "id1772"} d#0 != null;
    assert {:id "id1773"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id1774"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
    assert {:id "id1775"} d#0 != null;
    assume true;
    assert {:id "id1776"} d#0 != null;
    assert {:id "id1777"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id1778"} $Unbox(read($Heap, d#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
    assert {:id "id1779"} d#0 != null;
    assume true;
    assert {:id "id1780"} d#0 != null;
    assert {:id "id1781"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id1782"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
    assert {:id "id1783"} e#0 != null;
    assume true;
    assert {:id "id1784"} e#0 != null;
    assert {:id "id1785"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id1786"} $Unbox(read($Heap, e#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.val)): int
         + Mul(LitInt(2), m#0)
         + Mul(LitInt(4), n#0)
         + 8;
    assert {:id "id1787"} e#0 != null;
    assume true;
    assert {:id "id1788"} e#0 != null;
    assert {:id "id1789"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id1790"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
    assert {:id "id1791"} e#0 != null;
    assume true;
    assert {:id "id1792"} e#0 != null;
    assert {:id "id1793"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id1794"} $Unbox(read($Heap, e#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
    assert {:id "id1795"} e#0 != null;
    assume true;
    assert {:id "id1796"} e#0 != null;
    assert {:id "id1797"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id1798"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
    assert {:id "id1799"} f#0 != null;
    assume true;
    assert {:id "id1800"} f#0 != null;
    assert {:id "id1801"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id1802"} $Unbox(read($Heap, f#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.val)): int
         + Mul(LitInt(2), m#0)
         + Mul(LitInt(4), n#0)
         + 8;
    assert {:id "id1803"} f#0 != null;
    assume true;
    assert {:id "id1804"} f#0 != null;
    assert {:id "id1805"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id1806"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
    assert {:id "id1807"} f#0 != null;
    assume true;
    assert {:id "id1808"} f#0 != null;
    assert {:id "id1809"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id1810"} $Unbox(read($Heap, f#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
    assert {:id "id1811"} f#0 != null;
    assume true;
    assert {:id "id1812"} f#0 != null;
    assert {:id "id1813"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id1814"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
    assert {:id "id1815"} p#0 != null;
    assume true;
    assert {:id "id1816"} p#0 != null;
    assert {:id "id1817"} p#0 == null || old($Alloc)[p#0];
    assume true;
    assume {:id "id1818"} $Unbox(read($Heap, p#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), p#0, _module.Node.val)): int + 5;
    assert {:id "id1819"} p#0 != null;
    assume true;
    assert {:id "id1820"} p#0 != null;
    assert {:id "id1821"} p#0 == null || old($Alloc)[p#0];
    assume true;
    assume {:id "id1822"} $Unbox(read($Heap, p#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), p#0, _module.Node.tag)): int;
    assert {:id "id1823"} p#0 != null;
    assume true;
    assert {:id "id1824"} p#0 != null;
    assert {:id "id1825"} p#0 == null || old($Alloc)[p#0];
    assume true;
    assume {:id "id1826"} $Unbox(read($Heap, p#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), p#0, _module.Node.score)): int;
    assert {:id "id1827"} p#0 != null;
    assume true;
    assert {:id "id1828"} p#0 != null;
    assert {:id "id1829"} p#0 == null || old($Alloc)[p#0];
    assume true;
    assume {:id "id1830"} $Unbox(read($Heap, p#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), p#0, _module.Node.rank)): int;
    assert {:id "id1831"} q#0 != null;
    assume true;
    assert {:id "id1832"} q#0 != null;
    assert {:id "id1833"} q#0 == null || old($Alloc)[q#0];
    assume true;
    assume {:id "id1834"} $Unbox(read($Heap, q#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), q#0, _module.Node.val)): int + 5;
    assert {:id "id1835"} q#0 != null;
    assume true;
    assert {:id "id1836"} q#0 != null;
    assert {:id "id1837"} q#0 == null || old($Alloc)[q#0];
    assume true;
    assume {:id "id1838"} $Unbox(read($Heap, q#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), q#0, _module.Node.tag)): int;
    assert {:id "id1839"} q#0 != null;
    assume true;
    assert {:id "id1840"} q#0 != null;
    assert {:id "id1841"} q#0 == null || old($Alloc)[q#0];
    assume true;
    assume {:id "id1842"} $Unbox(read($Heap, q#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), q#0, _module.Node.score)): int;
    assert {:id "id1843"} q#0 != null;
    assume true;
    assert {:id "id1844"} q#0 != null;
    assert {:id "id1845"} q#0 == null || old($Alloc)[q#0];
    assume true;
    assume {:id "id1846"} $Unbox(read($Heap, q#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), q#0, _module.Node.rank)): int;
    assert {:id "id1847"} r#0 != null;
    assume true;
    assert {:id "id1848"} r#0 != null;
    assert {:id "id1849"} r#0 == null || old($Alloc)[r#0];
    assume true;
    assume {:id "id1850"} $Unbox(read($Heap, r#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), r#0, _module.Node.val)): int + 5;
    assert {:id "id1851"} r#0 != null;
    assume true;
    assert {:id "id1852"} r#0 != null;
    assert {:id "id1853"} r#0 == null || old($Alloc)[r#0];
    assume true;
    assume {:id "id1854"} $Unbox(read($Heap, r#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), r#0, _module.Node.tag)): int;
    assert {:id "id1855"} r#0 != null;
    assume true;
    assert {:id "id1856"} r#0 != null;
    assert {:id "id1857"} r#0 == null || old($Alloc)[r#0];
    assume true;
    assume {:id "id1858"} $Unbox(read($Heap, r#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), r#0, _module.Node.score)): int;
    assert {:id "id1859"} r#0 != null;
    assume true;
    assert {:id "id1860"} r#0 != null;
    assert {:id "id1861"} r#0 == null || old($Alloc)[r#0];
    assume true;
    assume {:id "id1862"} $Unbox(read($Heap, r#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), r#0, _module.Node.rank)): int;
    assert {:id "id1863"} s#0 != null;
    assume true;
    assert {:id "id1864"} s#0 != null;
    assert {:id "id1865"} s#0 == null || old($Alloc)[s#0];
    assume true;
    assume {:id "id1866"} $Unbox(read($Heap, s#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), s#0, _module.Node.val)): int + 4;
    assert {:id "id1867"} s#0 != null;
    assume true;
    assert {:id "id1868"} s#0 != null;
    assert {:id "id1869"} s#0 == null || old($Alloc)[s#0];
    assume true;
    assume {:id "id1870"} $Unbox(read($Heap, s#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), s#0, _module.Node.tag)): int;
    assert {:id "id1871"} s#0 != null;
    assume true;
    assert {:id "id1872"} s#0 != null;
    assert {:id "id1873"} s#0 == null || old($Alloc)[s#0];
    assume true;
    assume {:id "id1874"} $Unbox(read($Heap, s#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), s#0, _module.Node.score)): int;
    assert {:id "id1875"} s#0 != null;
    assume true;
    assert {:id "id1876"} s#0 != null;
    assert {:id "id1877"} s#0 == null || old($Alloc)[s#0];
    assume true;
    assume {:id "id1878"} $Unbox(read($Heap, s#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), s#0, _module.Node.rank)): int;
    assert {:id "id1879"} t#0 != null;
    assume true;
    assert {:id "id1880"} t#0 != null;
    assert {:id "id1881"} t#0 == null || old($Alloc)[t#0];
    assume true;
    assume {:id "id1882"} $Unbox(read($Heap, t#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), t#0, _module.Node.val)): int + 4;
    assert {:id "id1883"} t#0 != null;
    assume true;
    assert {:id "id1884"} t#0 != null;
    assert {:id "id1885"} t#0 == null || old($Alloc)[t#0];
    assume true;
    assume {:id "id1886"} $Unbox(read($Heap, t#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), t#0, _module.Node.tag)): int;
    assert {:id "id1887"} t#0 != null;
    assume true;
    assert {:id "id1888"} t#0 != null;
    assert {:id "id1889"} t#0 == null || old($Alloc)[t#0];
    assume true;
    assume {:id "id1890"} $Unbox(read($Heap, t#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), t#0, _module.Node.score)): int;
    assert {:id "id1891"} t#0 != null;
    assume true;
    assert {:id "id1892"} t#0 != null;
    assert {:id "id1893"} t#0 == null || old($Alloc)[t#0];
    assume true;
    assume {:id "id1894"} $Unbox(read($Heap, t#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), t#0, _module.Node.rank)): int;
    assert {:id "id1895"} u#0 != null;
    assume true;
    assert {:id "id1896"} u#0 != null;
    assert {:id "id1897"} u#0 == null || old($Alloc)[u#0];
    assume true;
    assume {:id "id1898"} $Unbox(read($Heap, u#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), u#0, _module.Node.val)): int + 4;
    assert {:id "id1899"} u#0 != null;
    assume true;
    assert {:id "id1900"} u#0 != null;
    assert {:id "id1901"} u#0 == null || old($Alloc)[u#0];
    assume true;
    assume {:id "id1902"} $Unbox(read($Heap, u#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), u#0, _module.Node.tag)): int;
    assert {:id "id1903"} u#0 != null;
    assume true;
    assert {:id "id1904"} u#0 != null;
    assert {:id "id1905"} u#0 == null || old($Alloc)[u#0];
    assume true;
    assume {:id "id1906"} $Unbox(read($Heap, u#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), u#0, _module.Node.score)): int;
    assert {:id "id1907"} u#0 != null;
    assume true;
    assert {:id "id1908"} u#0 != null;
    assert {:id "id1909"} u#0 == null || old($Alloc)[u#0];
    assume true;
    assume {:id "id1910"} $Unbox(read($Heap, u#0, _module.Node.rank)): int
       == $Unbox(read(old($Heap), u#0, _module.Node.rank)): int;
}



procedure {:verboseName "StressTest (call)"} Call$$_module.__default.StressTest(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]), 
    p#0: ref where $Is(p#0, Tclass._module.Node()) && (p#0 == null || $Alloc[p#0]), 
    q#0: ref where $Is(q#0, Tclass._module.Node()) && (q#0 == null || $Alloc[q#0]), 
    r#0: ref where $Is(r#0, Tclass._module.Node()) && (r#0 == null || $Alloc[r#0]), 
    s#0: ref where $Is(s#0, Tclass._module.Node()) && (s#0 == null || $Alloc[s#0]), 
    t#0: ref where $Is(t#0, Tclass._module.Node()) && (t#0 == null || $Alloc[t#0]), 
    u#0: ref where $Is(u#0, Tclass._module.Node()) && (u#0 == null || $Alloc[u#0]), 
    m#0: int, 
    n#0: int);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id1911"} m#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id1912"} n#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id1913"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id1914"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1915"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1916"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1917"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1918"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1919"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1920"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1921"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1922"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1923"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1924"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1925"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1926"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1927"} e#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1928"} p#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1929"} p#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1930"} p#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1931"} p#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1932"} p#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1933"} q#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1934"} q#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1935"} q#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1936"} q#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1937"} r#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1938"} r#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1939"} r#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1940"} s#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1941"} s#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1942"} t#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1943"} a#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1944"} a#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1945"} a#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1946"} a#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1947"} a#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1948"} a#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1949"} b#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1950"} b#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1951"} b#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1952"} b#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1953"} b#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1954"} b#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1955"} c#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1956"} c#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1957"} c#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1958"} c#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1959"} c#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1960"} c#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1961"} d#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1962"} d#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1963"} d#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1964"} d#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1965"} d#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1966"} d#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1967"} e#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1968"} e#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1969"} e#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1970"} e#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1971"} e#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1972"} e#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1973"} f#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1974"} f#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1975"} f#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1976"} f#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1977"} f#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1978"} f#0 != u#0;
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
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id1979"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 9;
  free ensures {:always_assume} true;
  ensures {:id "id1980"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1981"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1982"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1983"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 9;
  free ensures {:always_assume} true;
  ensures {:id "id1984"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1985"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1986"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1987"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 9;
  free ensures {:always_assume} true;
  ensures {:id "id1988"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1989"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1990"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1991"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 8;
  free ensures {:always_assume} true;
  ensures {:id "id1992"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1993"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1994"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1995"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 8;
  free ensures {:always_assume} true;
  ensures {:id "id1996"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1997"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1998"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1999"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 8;
  free ensures {:always_assume} true;
  ensures {:id "id2000"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2001"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2002"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2003"} $Unbox(read($Heap, p#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.val)): int + 5;
  free ensures {:always_assume} true;
  ensures {:id "id2004"} $Unbox(read($Heap, p#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2005"} $Unbox(read($Heap, p#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2006"} $Unbox(read($Heap, p#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2007"} $Unbox(read($Heap, q#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.val)): int + 5;
  free ensures {:always_assume} true;
  ensures {:id "id2008"} $Unbox(read($Heap, q#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2009"} $Unbox(read($Heap, q#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2010"} $Unbox(read($Heap, q#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2011"} $Unbox(read($Heap, r#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.val)): int + 5;
  free ensures {:always_assume} true;
  ensures {:id "id2012"} $Unbox(read($Heap, r#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2013"} $Unbox(read($Heap, r#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2014"} $Unbox(read($Heap, r#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2015"} $Unbox(read($Heap, s#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id2016"} $Unbox(read($Heap, s#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2017"} $Unbox(read($Heap, s#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2018"} $Unbox(read($Heap, s#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2019"} $Unbox(read($Heap, t#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id2020"} $Unbox(read($Heap, t#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2021"} $Unbox(read($Heap, t#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2022"} $Unbox(read($Heap, t#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2023"} $Unbox(read($Heap, u#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id2024"} $Unbox(read($Heap, u#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2025"} $Unbox(read($Heap, u#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2026"} $Unbox(read($Heap, u#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.rank)): int;



procedure {:verboseName "StressTest (correctness)"} Impl$$_module.__default.StressTest(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]), 
    p#0: ref where $Is(p#0, Tclass._module.Node()) && (p#0 == null || $Alloc[p#0]), 
    q#0: ref where $Is(q#0, Tclass._module.Node()) && (q#0 == null || $Alloc[q#0]), 
    r#0: ref where $Is(r#0, Tclass._module.Node()) && (r#0 == null || $Alloc[r#0]), 
    s#0: ref where $Is(s#0, Tclass._module.Node()) && (s#0 == null || $Alloc[s#0]), 
    t#0: ref where $Is(t#0, Tclass._module.Node()) && (t#0 == null || $Alloc[t#0]), 
    u#0: ref where $Is(u#0, Tclass._module.Node()) && (u#0 == null || $Alloc[u#0]), 
    m#0: int, 
    n#0: int)
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id2027"} m#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id2028"} n#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id2029"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id2030"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id2031"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id2032"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id2033"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id2034"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id2035"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id2036"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id2037"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id2038"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id2039"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id2040"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id2041"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id2042"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id2043"} e#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id2044"} p#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id2045"} p#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id2046"} p#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id2047"} p#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2048"} p#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2049"} q#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id2050"} q#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id2051"} q#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2052"} q#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2053"} r#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id2054"} r#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2055"} r#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2056"} s#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2057"} s#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2058"} t#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2059"} a#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id2060"} a#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id2061"} a#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id2062"} a#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id2063"} a#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2064"} a#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2065"} b#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id2066"} b#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id2067"} b#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id2068"} b#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id2069"} b#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2070"} b#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2071"} c#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id2072"} c#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id2073"} c#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id2074"} c#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id2075"} c#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2076"} c#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2077"} d#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id2078"} d#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id2079"} d#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id2080"} d#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id2081"} d#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2082"} d#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2083"} e#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id2084"} e#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id2085"} e#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id2086"} e#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id2087"} e#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2088"} e#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id2089"} f#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id2090"} f#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id2091"} f#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id2092"} f#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id2093"} f#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id2094"} f#0 != u#0;
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
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id2095"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 9;
  free ensures {:always_assume} true;
  ensures {:id "id2096"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2097"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2098"} $Unbox(read($Heap, a#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2099"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 9;
  free ensures {:always_assume} true;
  ensures {:id "id2100"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2101"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2102"} $Unbox(read($Heap, b#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2103"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 9;
  free ensures {:always_assume} true;
  ensures {:id "id2104"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2105"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2106"} $Unbox(read($Heap, c#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2107"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 8;
  free ensures {:always_assume} true;
  ensures {:id "id2108"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2109"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2110"} $Unbox(read($Heap, d#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2111"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 8;
  free ensures {:always_assume} true;
  ensures {:id "id2112"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2113"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2114"} $Unbox(read($Heap, e#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2115"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int
       + Mul(LitInt(2), m#0)
       + Mul(LitInt(4), n#0)
       + 8;
  free ensures {:always_assume} true;
  ensures {:id "id2116"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2117"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2118"} $Unbox(read($Heap, f#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2119"} $Unbox(read($Heap, p#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.val)): int + 5;
  free ensures {:always_assume} true;
  ensures {:id "id2120"} $Unbox(read($Heap, p#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2121"} $Unbox(read($Heap, p#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2122"} $Unbox(read($Heap, p#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2123"} $Unbox(read($Heap, q#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.val)): int + 5;
  free ensures {:always_assume} true;
  ensures {:id "id2124"} $Unbox(read($Heap, q#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2125"} $Unbox(read($Heap, q#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2126"} $Unbox(read($Heap, q#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2127"} $Unbox(read($Heap, r#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.val)): int + 5;
  free ensures {:always_assume} true;
  ensures {:id "id2128"} $Unbox(read($Heap, r#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2129"} $Unbox(read($Heap, r#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2130"} $Unbox(read($Heap, r#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2131"} $Unbox(read($Heap, s#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id2132"} $Unbox(read($Heap, s#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2133"} $Unbox(read($Heap, s#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2134"} $Unbox(read($Heap, s#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2135"} $Unbox(read($Heap, t#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id2136"} $Unbox(read($Heap, t#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2137"} $Unbox(read($Heap, t#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2138"} $Unbox(read($Heap, t#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.rank)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2139"} $Unbox(read($Heap, u#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id2140"} $Unbox(read($Heap, u#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2141"} $Unbox(read($Heap, u#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id2142"} $Unbox(read($Heap, u#0, _module.Node.rank)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.rank)): int;



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
  var a##0: ref;
  var b##0: ref;
  var c##0: ref;
  var d##0: ref;
  var e##0: ref;
  var f##0: ref;
  var n##0: int;
  var $PreCallHeap#0: Heap;
  var $PreCallAlloc#0: [ref]bool;
  var a##1: ref;
  var b##1: ref;
  var c##1: ref;
  var d##1: ref;
  var e##1: ref;
  var f##1: ref;
  var n##1: int;
  var $PreCallHeap#1: Heap;
  var $PreCallAlloc#1: [ref]bool;
  var a##2: ref;
  var b##2: ref;
  var c##2: ref;
  var d##2: ref;
  var e##2: ref;
  var f##2: ref;
  var $PreCallHeap#2: Heap;
  var $PreCallAlloc#2: [ref]bool;
  var a##3: ref;
  var b##3: ref;
  var c##3: ref;
  var p##0: ref;
  var q##0: ref;
  var r##0: ref;
  var $PreCallHeap#3: Heap;
  var $PreCallAlloc#3: [ref]bool;
  var a##4: ref;
  var b##4: ref;
  var c##4: ref;
  var d##3: ref;
  var e##3: ref;
  var f##3: ref;
  var $PreCallHeap#4: Heap;
  var $PreCallAlloc#4: [ref]bool;

    // AddMethodImpl: StressTest, Impl$$_module.__default.StressTest
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
    $PreCallHeap#0 := $Heap;
    $PreCallAlloc#0 := $Alloc;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id2143"} a##0 == a#0
       || a##0 == b#0
       || a##0 == c#0
       || a##0 == d#0
       || a##0 == e#0
       || a##0 == f#0
       || a##0 == p#0
       || a##0 == q#0
       || a##0 == r#0
       || a##0 == s#0
       || a##0 == t#0
       || a##0 == u#0
       || !old($Alloc)[a##0];
    assert {:id "id2144"} b##0 == a#0
       || b##0 == b#0
       || b##0 == c#0
       || b##0 == d#0
       || b##0 == e#0
       || b##0 == f#0
       || b##0 == p#0
       || b##0 == q#0
       || b##0 == r#0
       || b##0 == s#0
       || b##0 == t#0
       || b##0 == u#0
       || !old($Alloc)[b##0];
    assert {:id "id2145"} c##0 == a#0
       || c##0 == b#0
       || c##0 == c#0
       || c##0 == d#0
       || c##0 == e#0
       || c##0 == f#0
       || c##0 == p#0
       || c##0 == q#0
       || c##0 == r#0
       || c##0 == s#0
       || c##0 == t#0
       || c##0 == u#0
       || !old($Alloc)[c##0];
    assert {:id "id2146"} d##0 == a#0
       || d##0 == b#0
       || d##0 == c#0
       || d##0 == d#0
       || d##0 == e#0
       || d##0 == f#0
       || d##0 == p#0
       || d##0 == q#0
       || d##0 == r#0
       || d##0 == s#0
       || d##0 == t#0
       || d##0 == u#0
       || !old($Alloc)[d##0];
    assert {:id "id2147"} e##0 == a#0
       || e##0 == b#0
       || e##0 == c#0
       || e##0 == d#0
       || e##0 == e#0
       || e##0 == f#0
       || e##0 == p#0
       || e##0 == q#0
       || e##0 == r#0
       || e##0 == s#0
       || e##0 == t#0
       || e##0 == u#0
       || !old($Alloc)[e##0];
    assert {:id "id2148"} f##0 == a#0
       || f##0 == b#0
       || f##0 == c#0
       || f##0 == d#0
       || f##0 == e#0
       || f##0 == f#0
       || f##0 == p#0
       || f##0 == q#0
       || f##0 == r#0
       || f##0 == s#0
       || f##0 == t#0
       || f##0 == u#0
       || !old($Alloc)[f##0];
    call {:id "id2149"} Call$$_module.__default.BumpN(a##0, b##0, c##0, d##0, e##0, f##0, n##0);
    // qf-call-frame BumpN: supports=18 reads=72 modified=6
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.val)
         == read($PreCallHeap#0, a#0, _module.Node.val);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.tag)
         == read($PreCallHeap#0, a#0, _module.Node.tag);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.score)
         == read($PreCallHeap#0, a#0, _module.Node.score);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.rank)
         == read($PreCallHeap#0, a#0, _module.Node.rank);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.val)
         == read($PreCallHeap#0, b#0, _module.Node.val);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.tag)
         == read($PreCallHeap#0, b#0, _module.Node.tag);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.score)
         == read($PreCallHeap#0, b#0, _module.Node.score);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.rank)
         == read($PreCallHeap#0, b#0, _module.Node.rank);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.val)
         == read($PreCallHeap#0, c#0, _module.Node.val);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.tag)
         == read($PreCallHeap#0, c#0, _module.Node.tag);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.score)
         == read($PreCallHeap#0, c#0, _module.Node.score);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.rank)
         == read($PreCallHeap#0, c#0, _module.Node.rank);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.val)
         == read($PreCallHeap#0, d#0, _module.Node.val);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.tag)
         == read($PreCallHeap#0, d#0, _module.Node.tag);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.score)
         == read($PreCallHeap#0, d#0, _module.Node.score);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.rank)
         == read($PreCallHeap#0, d#0, _module.Node.rank);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.val)
         == read($PreCallHeap#0, e#0, _module.Node.val);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.tag)
         == read($PreCallHeap#0, e#0, _module.Node.tag);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.score)
         == read($PreCallHeap#0, e#0, _module.Node.score);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.rank)
         == read($PreCallHeap#0, e#0, _module.Node.rank);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.val)
         == read($PreCallHeap#0, f#0, _module.Node.val);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.tag)
         == read($PreCallHeap#0, f#0, _module.Node.tag);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.score)
         == read($PreCallHeap#0, f#0, _module.Node.score);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.rank)
         == read($PreCallHeap#0, f#0, _module.Node.rank);
    assume p#0 != null
         && p#0 != a#0
         && p#0 != b#0
         && p#0 != c#0
         && p#0 != d#0
         && p#0 != e#0
         && p#0 != f#0
       ==> read($Heap, p#0, _module.Node.val)
         == read($PreCallHeap#0, p#0, _module.Node.val);
    assume p#0 != null
         && p#0 != a#0
         && p#0 != b#0
         && p#0 != c#0
         && p#0 != d#0
         && p#0 != e#0
         && p#0 != f#0
       ==> read($Heap, p#0, _module.Node.tag)
         == read($PreCallHeap#0, p#0, _module.Node.tag);
    assume p#0 != null
         && p#0 != a#0
         && p#0 != b#0
         && p#0 != c#0
         && p#0 != d#0
         && p#0 != e#0
         && p#0 != f#0
       ==> read($Heap, p#0, _module.Node.score)
         == read($PreCallHeap#0, p#0, _module.Node.score);
    assume p#0 != null
         && p#0 != a#0
         && p#0 != b#0
         && p#0 != c#0
         && p#0 != d#0
         && p#0 != e#0
         && p#0 != f#0
       ==> read($Heap, p#0, _module.Node.rank)
         == read($PreCallHeap#0, p#0, _module.Node.rank);
    assume q#0 != null
         && q#0 != a#0
         && q#0 != b#0
         && q#0 != c#0
         && q#0 != d#0
         && q#0 != e#0
         && q#0 != f#0
       ==> read($Heap, q#0, _module.Node.val)
         == read($PreCallHeap#0, q#0, _module.Node.val);
    assume q#0 != null
         && q#0 != a#0
         && q#0 != b#0
         && q#0 != c#0
         && q#0 != d#0
         && q#0 != e#0
         && q#0 != f#0
       ==> read($Heap, q#0, _module.Node.tag)
         == read($PreCallHeap#0, q#0, _module.Node.tag);
    assume q#0 != null
         && q#0 != a#0
         && q#0 != b#0
         && q#0 != c#0
         && q#0 != d#0
         && q#0 != e#0
         && q#0 != f#0
       ==> read($Heap, q#0, _module.Node.score)
         == read($PreCallHeap#0, q#0, _module.Node.score);
    assume q#0 != null
         && q#0 != a#0
         && q#0 != b#0
         && q#0 != c#0
         && q#0 != d#0
         && q#0 != e#0
         && q#0 != f#0
       ==> read($Heap, q#0, _module.Node.rank)
         == read($PreCallHeap#0, q#0, _module.Node.rank);
    assume r#0 != null
         && r#0 != a#0
         && r#0 != b#0
         && r#0 != c#0
         && r#0 != d#0
         && r#0 != e#0
         && r#0 != f#0
       ==> read($Heap, r#0, _module.Node.val)
         == read($PreCallHeap#0, r#0, _module.Node.val);
    assume r#0 != null
         && r#0 != a#0
         && r#0 != b#0
         && r#0 != c#0
         && r#0 != d#0
         && r#0 != e#0
         && r#0 != f#0
       ==> read($Heap, r#0, _module.Node.tag)
         == read($PreCallHeap#0, r#0, _module.Node.tag);
    assume r#0 != null
         && r#0 != a#0
         && r#0 != b#0
         && r#0 != c#0
         && r#0 != d#0
         && r#0 != e#0
         && r#0 != f#0
       ==> read($Heap, r#0, _module.Node.score)
         == read($PreCallHeap#0, r#0, _module.Node.score);
    assume r#0 != null
         && r#0 != a#0
         && r#0 != b#0
         && r#0 != c#0
         && r#0 != d#0
         && r#0 != e#0
         && r#0 != f#0
       ==> read($Heap, r#0, _module.Node.rank)
         == read($PreCallHeap#0, r#0, _module.Node.rank);
    assume s#0 != null
         && s#0 != a#0
         && s#0 != b#0
         && s#0 != c#0
         && s#0 != d#0
         && s#0 != e#0
         && s#0 != f#0
       ==> read($Heap, s#0, _module.Node.val)
         == read($PreCallHeap#0, s#0, _module.Node.val);
    assume s#0 != null
         && s#0 != a#0
         && s#0 != b#0
         && s#0 != c#0
         && s#0 != d#0
         && s#0 != e#0
         && s#0 != f#0
       ==> read($Heap, s#0, _module.Node.tag)
         == read($PreCallHeap#0, s#0, _module.Node.tag);
    assume s#0 != null
         && s#0 != a#0
         && s#0 != b#0
         && s#0 != c#0
         && s#0 != d#0
         && s#0 != e#0
         && s#0 != f#0
       ==> read($Heap, s#0, _module.Node.score)
         == read($PreCallHeap#0, s#0, _module.Node.score);
    assume s#0 != null
         && s#0 != a#0
         && s#0 != b#0
         && s#0 != c#0
         && s#0 != d#0
         && s#0 != e#0
         && s#0 != f#0
       ==> read($Heap, s#0, _module.Node.rank)
         == read($PreCallHeap#0, s#0, _module.Node.rank);
    assume t#0 != null
         && t#0 != a#0
         && t#0 != b#0
         && t#0 != c#0
         && t#0 != d#0
         && t#0 != e#0
         && t#0 != f#0
       ==> read($Heap, t#0, _module.Node.val)
         == read($PreCallHeap#0, t#0, _module.Node.val);
    assume t#0 != null
         && t#0 != a#0
         && t#0 != b#0
         && t#0 != c#0
         && t#0 != d#0
         && t#0 != e#0
         && t#0 != f#0
       ==> read($Heap, t#0, _module.Node.tag)
         == read($PreCallHeap#0, t#0, _module.Node.tag);
    assume t#0 != null
         && t#0 != a#0
         && t#0 != b#0
         && t#0 != c#0
         && t#0 != d#0
         && t#0 != e#0
         && t#0 != f#0
       ==> read($Heap, t#0, _module.Node.score)
         == read($PreCallHeap#0, t#0, _module.Node.score);
    assume t#0 != null
         && t#0 != a#0
         && t#0 != b#0
         && t#0 != c#0
         && t#0 != d#0
         && t#0 != e#0
         && t#0 != f#0
       ==> read($Heap, t#0, _module.Node.rank)
         == read($PreCallHeap#0, t#0, _module.Node.rank);
    assume u#0 != null
         && u#0 != a#0
         && u#0 != b#0
         && u#0 != c#0
         && u#0 != d#0
         && u#0 != e#0
         && u#0 != f#0
       ==> read($Heap, u#0, _module.Node.val)
         == read($PreCallHeap#0, u#0, _module.Node.val);
    assume u#0 != null
         && u#0 != a#0
         && u#0 != b#0
         && u#0 != c#0
         && u#0 != d#0
         && u#0 != e#0
         && u#0 != f#0
       ==> read($Heap, u#0, _module.Node.tag)
         == read($PreCallHeap#0, u#0, _module.Node.tag);
    assume u#0 != null
         && u#0 != a#0
         && u#0 != b#0
         && u#0 != c#0
         && u#0 != d#0
         && u#0 != e#0
         && u#0 != f#0
       ==> read($Heap, u#0, _module.Node.score)
         == read($PreCallHeap#0, u#0, _module.Node.score);
    assume u#0 != null
         && u#0 != a#0
         && u#0 != b#0
         && u#0 != c#0
         && u#0 != d#0
         && u#0 != e#0
         && u#0 != f#0
       ==> read($Heap, u#0, _module.Node.rank)
         == read($PreCallHeap#0, u#0, _module.Node.rank);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.val)
         == read($PreCallHeap#0, a##0, _module.Node.val);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.tag)
         == read($PreCallHeap#0, a##0, _module.Node.tag);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.score)
         == read($PreCallHeap#0, a##0, _module.Node.score);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.rank)
         == read($PreCallHeap#0, a##0, _module.Node.rank);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.val)
         == read($PreCallHeap#0, b##0, _module.Node.val);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.tag)
         == read($PreCallHeap#0, b##0, _module.Node.tag);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.score)
         == read($PreCallHeap#0, b##0, _module.Node.score);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.rank)
         == read($PreCallHeap#0, b##0, _module.Node.rank);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.val)
         == read($PreCallHeap#0, c##0, _module.Node.val);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.tag)
         == read($PreCallHeap#0, c##0, _module.Node.tag);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.score)
         == read($PreCallHeap#0, c##0, _module.Node.score);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.rank)
         == read($PreCallHeap#0, c##0, _module.Node.rank);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.val)
         == read($PreCallHeap#0, d##0, _module.Node.val);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.tag)
         == read($PreCallHeap#0, d##0, _module.Node.tag);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.score)
         == read($PreCallHeap#0, d##0, _module.Node.score);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.rank)
         == read($PreCallHeap#0, d##0, _module.Node.rank);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.val)
         == read($PreCallHeap#0, e##0, _module.Node.val);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.tag)
         == read($PreCallHeap#0, e##0, _module.Node.tag);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.score)
         == read($PreCallHeap#0, e##0, _module.Node.score);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.rank)
         == read($PreCallHeap#0, e##0, _module.Node.rank);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.val)
         == read($PreCallHeap#0, f##0, _module.Node.val);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.tag)
         == read($PreCallHeap#0, f##0, _module.Node.tag);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.score)
         == read($PreCallHeap#0, f##0, _module.Node.score);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.rank)
         == read($PreCallHeap#0, f##0, _module.Node.rank);
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
    $PreCallHeap#1 := $Heap;
    $PreCallAlloc#1 := $Alloc;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id2150"} a##1 == a#0
       || a##1 == b#0
       || a##1 == c#0
       || a##1 == d#0
       || a##1 == e#0
       || a##1 == f#0
       || a##1 == p#0
       || a##1 == q#0
       || a##1 == r#0
       || a##1 == s#0
       || a##1 == t#0
       || a##1 == u#0
       || !old($Alloc)[a##1];
    assert {:id "id2151"} b##1 == a#0
       || b##1 == b#0
       || b##1 == c#0
       || b##1 == d#0
       || b##1 == e#0
       || b##1 == f#0
       || b##1 == p#0
       || b##1 == q#0
       || b##1 == r#0
       || b##1 == s#0
       || b##1 == t#0
       || b##1 == u#0
       || !old($Alloc)[b##1];
    assert {:id "id2152"} c##1 == a#0
       || c##1 == b#0
       || c##1 == c#0
       || c##1 == d#0
       || c##1 == e#0
       || c##1 == f#0
       || c##1 == p#0
       || c##1 == q#0
       || c##1 == r#0
       || c##1 == s#0
       || c##1 == t#0
       || c##1 == u#0
       || !old($Alloc)[c##1];
    assert {:id "id2153"} d##1 == a#0
       || d##1 == b#0
       || d##1 == c#0
       || d##1 == d#0
       || d##1 == e#0
       || d##1 == f#0
       || d##1 == p#0
       || d##1 == q#0
       || d##1 == r#0
       || d##1 == s#0
       || d##1 == t#0
       || d##1 == u#0
       || !old($Alloc)[d##1];
    assert {:id "id2154"} e##1 == a#0
       || e##1 == b#0
       || e##1 == c#0
       || e##1 == d#0
       || e##1 == e#0
       || e##1 == f#0
       || e##1 == p#0
       || e##1 == q#0
       || e##1 == r#0
       || e##1 == s#0
       || e##1 == t#0
       || e##1 == u#0
       || !old($Alloc)[e##1];
    assert {:id "id2155"} f##1 == a#0
       || f##1 == b#0
       || f##1 == c#0
       || f##1 == d#0
       || f##1 == e#0
       || f##1 == f#0
       || f##1 == p#0
       || f##1 == q#0
       || f##1 == r#0
       || f##1 == s#0
       || f##1 == t#0
       || f##1 == u#0
       || !old($Alloc)[f##1];
    call {:id "id2156"} Call$$_module.__default.BumpNQuad(a##1, b##1, c##1, d##1, e##1, f##1, n##1);
    // qf-call-frame BumpNQuad: supports=24 reads=96 modified=6
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.val)
         == read($PreCallHeap#1, a#0, _module.Node.val);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.tag)
         == read($PreCallHeap#1, a#0, _module.Node.tag);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.score)
         == read($PreCallHeap#1, a#0, _module.Node.score);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.rank)
         == read($PreCallHeap#1, a#0, _module.Node.rank);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.val)
         == read($PreCallHeap#1, b#0, _module.Node.val);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.tag)
         == read($PreCallHeap#1, b#0, _module.Node.tag);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.score)
         == read($PreCallHeap#1, b#0, _module.Node.score);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.rank)
         == read($PreCallHeap#1, b#0, _module.Node.rank);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.val)
         == read($PreCallHeap#1, c#0, _module.Node.val);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.tag)
         == read($PreCallHeap#1, c#0, _module.Node.tag);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.score)
         == read($PreCallHeap#1, c#0, _module.Node.score);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.rank)
         == read($PreCallHeap#1, c#0, _module.Node.rank);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.val)
         == read($PreCallHeap#1, d#0, _module.Node.val);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.tag)
         == read($PreCallHeap#1, d#0, _module.Node.tag);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.score)
         == read($PreCallHeap#1, d#0, _module.Node.score);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.rank)
         == read($PreCallHeap#1, d#0, _module.Node.rank);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.val)
         == read($PreCallHeap#1, e#0, _module.Node.val);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.tag)
         == read($PreCallHeap#1, e#0, _module.Node.tag);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.score)
         == read($PreCallHeap#1, e#0, _module.Node.score);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.rank)
         == read($PreCallHeap#1, e#0, _module.Node.rank);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.val)
         == read($PreCallHeap#1, f#0, _module.Node.val);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.tag)
         == read($PreCallHeap#1, f#0, _module.Node.tag);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.score)
         == read($PreCallHeap#1, f#0, _module.Node.score);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.rank)
         == read($PreCallHeap#1, f#0, _module.Node.rank);
    assume p#0 != null
         && p#0 != a#0
         && p#0 != b#0
         && p#0 != c#0
         && p#0 != d#0
         && p#0 != e#0
         && p#0 != f#0
       ==> read($Heap, p#0, _module.Node.val)
         == read($PreCallHeap#1, p#0, _module.Node.val);
    assume p#0 != null
         && p#0 != a#0
         && p#0 != b#0
         && p#0 != c#0
         && p#0 != d#0
         && p#0 != e#0
         && p#0 != f#0
       ==> read($Heap, p#0, _module.Node.tag)
         == read($PreCallHeap#1, p#0, _module.Node.tag);
    assume p#0 != null
         && p#0 != a#0
         && p#0 != b#0
         && p#0 != c#0
         && p#0 != d#0
         && p#0 != e#0
         && p#0 != f#0
       ==> read($Heap, p#0, _module.Node.score)
         == read($PreCallHeap#1, p#0, _module.Node.score);
    assume p#0 != null
         && p#0 != a#0
         && p#0 != b#0
         && p#0 != c#0
         && p#0 != d#0
         && p#0 != e#0
         && p#0 != f#0
       ==> read($Heap, p#0, _module.Node.rank)
         == read($PreCallHeap#1, p#0, _module.Node.rank);
    assume q#0 != null
         && q#0 != a#0
         && q#0 != b#0
         && q#0 != c#0
         && q#0 != d#0
         && q#0 != e#0
         && q#0 != f#0
       ==> read($Heap, q#0, _module.Node.val)
         == read($PreCallHeap#1, q#0, _module.Node.val);
    assume q#0 != null
         && q#0 != a#0
         && q#0 != b#0
         && q#0 != c#0
         && q#0 != d#0
         && q#0 != e#0
         && q#0 != f#0
       ==> read($Heap, q#0, _module.Node.tag)
         == read($PreCallHeap#1, q#0, _module.Node.tag);
    assume q#0 != null
         && q#0 != a#0
         && q#0 != b#0
         && q#0 != c#0
         && q#0 != d#0
         && q#0 != e#0
         && q#0 != f#0
       ==> read($Heap, q#0, _module.Node.score)
         == read($PreCallHeap#1, q#0, _module.Node.score);
    assume q#0 != null
         && q#0 != a#0
         && q#0 != b#0
         && q#0 != c#0
         && q#0 != d#0
         && q#0 != e#0
         && q#0 != f#0
       ==> read($Heap, q#0, _module.Node.rank)
         == read($PreCallHeap#1, q#0, _module.Node.rank);
    assume r#0 != null
         && r#0 != a#0
         && r#0 != b#0
         && r#0 != c#0
         && r#0 != d#0
         && r#0 != e#0
         && r#0 != f#0
       ==> read($Heap, r#0, _module.Node.val)
         == read($PreCallHeap#1, r#0, _module.Node.val);
    assume r#0 != null
         && r#0 != a#0
         && r#0 != b#0
         && r#0 != c#0
         && r#0 != d#0
         && r#0 != e#0
         && r#0 != f#0
       ==> read($Heap, r#0, _module.Node.tag)
         == read($PreCallHeap#1, r#0, _module.Node.tag);
    assume r#0 != null
         && r#0 != a#0
         && r#0 != b#0
         && r#0 != c#0
         && r#0 != d#0
         && r#0 != e#0
         && r#0 != f#0
       ==> read($Heap, r#0, _module.Node.score)
         == read($PreCallHeap#1, r#0, _module.Node.score);
    assume r#0 != null
         && r#0 != a#0
         && r#0 != b#0
         && r#0 != c#0
         && r#0 != d#0
         && r#0 != e#0
         && r#0 != f#0
       ==> read($Heap, r#0, _module.Node.rank)
         == read($PreCallHeap#1, r#0, _module.Node.rank);
    assume s#0 != null
         && s#0 != a#0
         && s#0 != b#0
         && s#0 != c#0
         && s#0 != d#0
         && s#0 != e#0
         && s#0 != f#0
       ==> read($Heap, s#0, _module.Node.val)
         == read($PreCallHeap#1, s#0, _module.Node.val);
    assume s#0 != null
         && s#0 != a#0
         && s#0 != b#0
         && s#0 != c#0
         && s#0 != d#0
         && s#0 != e#0
         && s#0 != f#0
       ==> read($Heap, s#0, _module.Node.tag)
         == read($PreCallHeap#1, s#0, _module.Node.tag);
    assume s#0 != null
         && s#0 != a#0
         && s#0 != b#0
         && s#0 != c#0
         && s#0 != d#0
         && s#0 != e#0
         && s#0 != f#0
       ==> read($Heap, s#0, _module.Node.score)
         == read($PreCallHeap#1, s#0, _module.Node.score);
    assume s#0 != null
         && s#0 != a#0
         && s#0 != b#0
         && s#0 != c#0
         && s#0 != d#0
         && s#0 != e#0
         && s#0 != f#0
       ==> read($Heap, s#0, _module.Node.rank)
         == read($PreCallHeap#1, s#0, _module.Node.rank);
    assume t#0 != null
         && t#0 != a#0
         && t#0 != b#0
         && t#0 != c#0
         && t#0 != d#0
         && t#0 != e#0
         && t#0 != f#0
       ==> read($Heap, t#0, _module.Node.val)
         == read($PreCallHeap#1, t#0, _module.Node.val);
    assume t#0 != null
         && t#0 != a#0
         && t#0 != b#0
         && t#0 != c#0
         && t#0 != d#0
         && t#0 != e#0
         && t#0 != f#0
       ==> read($Heap, t#0, _module.Node.tag)
         == read($PreCallHeap#1, t#0, _module.Node.tag);
    assume t#0 != null
         && t#0 != a#0
         && t#0 != b#0
         && t#0 != c#0
         && t#0 != d#0
         && t#0 != e#0
         && t#0 != f#0
       ==> read($Heap, t#0, _module.Node.score)
         == read($PreCallHeap#1, t#0, _module.Node.score);
    assume t#0 != null
         && t#0 != a#0
         && t#0 != b#0
         && t#0 != c#0
         && t#0 != d#0
         && t#0 != e#0
         && t#0 != f#0
       ==> read($Heap, t#0, _module.Node.rank)
         == read($PreCallHeap#1, t#0, _module.Node.rank);
    assume u#0 != null
         && u#0 != a#0
         && u#0 != b#0
         && u#0 != c#0
         && u#0 != d#0
         && u#0 != e#0
         && u#0 != f#0
       ==> read($Heap, u#0, _module.Node.val)
         == read($PreCallHeap#1, u#0, _module.Node.val);
    assume u#0 != null
         && u#0 != a#0
         && u#0 != b#0
         && u#0 != c#0
         && u#0 != d#0
         && u#0 != e#0
         && u#0 != f#0
       ==> read($Heap, u#0, _module.Node.tag)
         == read($PreCallHeap#1, u#0, _module.Node.tag);
    assume u#0 != null
         && u#0 != a#0
         && u#0 != b#0
         && u#0 != c#0
         && u#0 != d#0
         && u#0 != e#0
         && u#0 != f#0
       ==> read($Heap, u#0, _module.Node.score)
         == read($PreCallHeap#1, u#0, _module.Node.score);
    assume u#0 != null
         && u#0 != a#0
         && u#0 != b#0
         && u#0 != c#0
         && u#0 != d#0
         && u#0 != e#0
         && u#0 != f#0
       ==> read($Heap, u#0, _module.Node.rank)
         == read($PreCallHeap#1, u#0, _module.Node.rank);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.val)
         == read($PreCallHeap#1, a##0, _module.Node.val);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.tag)
         == read($PreCallHeap#1, a##0, _module.Node.tag);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.score)
         == read($PreCallHeap#1, a##0, _module.Node.score);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.rank)
         == read($PreCallHeap#1, a##0, _module.Node.rank);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.val)
         == read($PreCallHeap#1, b##0, _module.Node.val);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.tag)
         == read($PreCallHeap#1, b##0, _module.Node.tag);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.score)
         == read($PreCallHeap#1, b##0, _module.Node.score);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.rank)
         == read($PreCallHeap#1, b##0, _module.Node.rank);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.val)
         == read($PreCallHeap#1, c##0, _module.Node.val);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.tag)
         == read($PreCallHeap#1, c##0, _module.Node.tag);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.score)
         == read($PreCallHeap#1, c##0, _module.Node.score);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.rank)
         == read($PreCallHeap#1, c##0, _module.Node.rank);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.val)
         == read($PreCallHeap#1, d##0, _module.Node.val);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.tag)
         == read($PreCallHeap#1, d##0, _module.Node.tag);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.score)
         == read($PreCallHeap#1, d##0, _module.Node.score);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.rank)
         == read($PreCallHeap#1, d##0, _module.Node.rank);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.val)
         == read($PreCallHeap#1, e##0, _module.Node.val);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.tag)
         == read($PreCallHeap#1, e##0, _module.Node.tag);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.score)
         == read($PreCallHeap#1, e##0, _module.Node.score);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.rank)
         == read($PreCallHeap#1, e##0, _module.Node.rank);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.val)
         == read($PreCallHeap#1, f##0, _module.Node.val);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.tag)
         == read($PreCallHeap#1, f##0, _module.Node.tag);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.score)
         == read($PreCallHeap#1, f##0, _module.Node.score);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.rank)
         == read($PreCallHeap#1, f##0, _module.Node.rank);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.val)
         == read($PreCallHeap#1, a##1, _module.Node.val);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.tag)
         == read($PreCallHeap#1, a##1, _module.Node.tag);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.score)
         == read($PreCallHeap#1, a##1, _module.Node.score);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.rank)
         == read($PreCallHeap#1, a##1, _module.Node.rank);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.val)
         == read($PreCallHeap#1, b##1, _module.Node.val);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.tag)
         == read($PreCallHeap#1, b##1, _module.Node.tag);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.score)
         == read($PreCallHeap#1, b##1, _module.Node.score);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.rank)
         == read($PreCallHeap#1, b##1, _module.Node.rank);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.val)
         == read($PreCallHeap#1, c##1, _module.Node.val);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.tag)
         == read($PreCallHeap#1, c##1, _module.Node.tag);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.score)
         == read($PreCallHeap#1, c##1, _module.Node.score);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.rank)
         == read($PreCallHeap#1, c##1, _module.Node.rank);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.val)
         == read($PreCallHeap#1, d##1, _module.Node.val);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.tag)
         == read($PreCallHeap#1, d##1, _module.Node.tag);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.score)
         == read($PreCallHeap#1, d##1, _module.Node.score);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.rank)
         == read($PreCallHeap#1, d##1, _module.Node.rank);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.val)
         == read($PreCallHeap#1, e##1, _module.Node.val);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.tag)
         == read($PreCallHeap#1, e##1, _module.Node.tag);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.score)
         == read($PreCallHeap#1, e##1, _module.Node.score);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.rank)
         == read($PreCallHeap#1, e##1, _module.Node.rank);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.val)
         == read($PreCallHeap#1, f##1, _module.Node.val);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.tag)
         == read($PreCallHeap#1, f##1, _module.Node.tag);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.score)
         == read($PreCallHeap#1, f##1, _module.Node.score);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.rank)
         == read($PreCallHeap#1, f##1, _module.Node.rank);
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
    $PreCallHeap#2 := $Heap;
    $PreCallAlloc#2 := $Alloc;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id2157"} a##2 == a#0
       || a##2 == b#0
       || a##2 == c#0
       || a##2 == d#0
       || a##2 == e#0
       || a##2 == f#0
       || a##2 == p#0
       || a##2 == q#0
       || a##2 == r#0
       || a##2 == s#0
       || a##2 == t#0
       || a##2 == u#0
       || !old($Alloc)[a##2];
    assert {:id "id2158"} b##2 == a#0
       || b##2 == b#0
       || b##2 == c#0
       || b##2 == d#0
       || b##2 == e#0
       || b##2 == f#0
       || b##2 == p#0
       || b##2 == q#0
       || b##2 == r#0
       || b##2 == s#0
       || b##2 == t#0
       || b##2 == u#0
       || !old($Alloc)[b##2];
    assert {:id "id2159"} c##2 == a#0
       || c##2 == b#0
       || c##2 == c#0
       || c##2 == d#0
       || c##2 == e#0
       || c##2 == f#0
       || c##2 == p#0
       || c##2 == q#0
       || c##2 == r#0
       || c##2 == s#0
       || c##2 == t#0
       || c##2 == u#0
       || !old($Alloc)[c##2];
    assert {:id "id2160"} d##2 == a#0
       || d##2 == b#0
       || d##2 == c#0
       || d##2 == d#0
       || d##2 == e#0
       || d##2 == f#0
       || d##2 == p#0
       || d##2 == q#0
       || d##2 == r#0
       || d##2 == s#0
       || d##2 == t#0
       || d##2 == u#0
       || !old($Alloc)[d##2];
    assert {:id "id2161"} e##2 == a#0
       || e##2 == b#0
       || e##2 == c#0
       || e##2 == d#0
       || e##2 == e#0
       || e##2 == f#0
       || e##2 == p#0
       || e##2 == q#0
       || e##2 == r#0
       || e##2 == s#0
       || e##2 == t#0
       || e##2 == u#0
       || !old($Alloc)[e##2];
    assert {:id "id2162"} f##2 == a#0
       || f##2 == b#0
       || f##2 == c#0
       || f##2 == d#0
       || f##2 == e#0
       || f##2 == f#0
       || f##2 == p#0
       || f##2 == q#0
       || f##2 == r#0
       || f##2 == s#0
       || f##2 == t#0
       || f##2 == u#0
       || !old($Alloc)[f##2];
    call {:id "id2163"} Call$$_module.__default.OctoBump(a##2, b##2, c##2, d##2, e##2, f##2);
    // qf-call-frame OctoBump: supports=30 reads=120 modified=6
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.val)
         == read($PreCallHeap#2, a#0, _module.Node.val);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.tag)
         == read($PreCallHeap#2, a#0, _module.Node.tag);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.score)
         == read($PreCallHeap#2, a#0, _module.Node.score);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != d#0
         && a#0 != e#0
         && a#0 != f#0
       ==> read($Heap, a#0, _module.Node.rank)
         == read($PreCallHeap#2, a#0, _module.Node.rank);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.val)
         == read($PreCallHeap#2, b#0, _module.Node.val);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.tag)
         == read($PreCallHeap#2, b#0, _module.Node.tag);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.score)
         == read($PreCallHeap#2, b#0, _module.Node.score);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != d#0
         && b#0 != e#0
         && b#0 != f#0
       ==> read($Heap, b#0, _module.Node.rank)
         == read($PreCallHeap#2, b#0, _module.Node.rank);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.val)
         == read($PreCallHeap#2, c#0, _module.Node.val);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.tag)
         == read($PreCallHeap#2, c#0, _module.Node.tag);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.score)
         == read($PreCallHeap#2, c#0, _module.Node.score);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != d#0
         && c#0 != e#0
         && c#0 != f#0
       ==> read($Heap, c#0, _module.Node.rank)
         == read($PreCallHeap#2, c#0, _module.Node.rank);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.val)
         == read($PreCallHeap#2, d#0, _module.Node.val);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.tag)
         == read($PreCallHeap#2, d#0, _module.Node.tag);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.score)
         == read($PreCallHeap#2, d#0, _module.Node.score);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != d#0
         && d#0 != e#0
         && d#0 != f#0
       ==> read($Heap, d#0, _module.Node.rank)
         == read($PreCallHeap#2, d#0, _module.Node.rank);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.val)
         == read($PreCallHeap#2, e#0, _module.Node.val);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.tag)
         == read($PreCallHeap#2, e#0, _module.Node.tag);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.score)
         == read($PreCallHeap#2, e#0, _module.Node.score);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != d#0
         && e#0 != e#0
         && e#0 != f#0
       ==> read($Heap, e#0, _module.Node.rank)
         == read($PreCallHeap#2, e#0, _module.Node.rank);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.val)
         == read($PreCallHeap#2, f#0, _module.Node.val);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.tag)
         == read($PreCallHeap#2, f#0, _module.Node.tag);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.score)
         == read($PreCallHeap#2, f#0, _module.Node.score);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != d#0
         && f#0 != e#0
         && f#0 != f#0
       ==> read($Heap, f#0, _module.Node.rank)
         == read($PreCallHeap#2, f#0, _module.Node.rank);
    assume p#0 != null
         && p#0 != a#0
         && p#0 != b#0
         && p#0 != c#0
         && p#0 != d#0
         && p#0 != e#0
         && p#0 != f#0
       ==> read($Heap, p#0, _module.Node.val)
         == read($PreCallHeap#2, p#0, _module.Node.val);
    assume p#0 != null
         && p#0 != a#0
         && p#0 != b#0
         && p#0 != c#0
         && p#0 != d#0
         && p#0 != e#0
         && p#0 != f#0
       ==> read($Heap, p#0, _module.Node.tag)
         == read($PreCallHeap#2, p#0, _module.Node.tag);
    assume p#0 != null
         && p#0 != a#0
         && p#0 != b#0
         && p#0 != c#0
         && p#0 != d#0
         && p#0 != e#0
         && p#0 != f#0
       ==> read($Heap, p#0, _module.Node.score)
         == read($PreCallHeap#2, p#0, _module.Node.score);
    assume p#0 != null
         && p#0 != a#0
         && p#0 != b#0
         && p#0 != c#0
         && p#0 != d#0
         && p#0 != e#0
         && p#0 != f#0
       ==> read($Heap, p#0, _module.Node.rank)
         == read($PreCallHeap#2, p#0, _module.Node.rank);
    assume q#0 != null
         && q#0 != a#0
         && q#0 != b#0
         && q#0 != c#0
         && q#0 != d#0
         && q#0 != e#0
         && q#0 != f#0
       ==> read($Heap, q#0, _module.Node.val)
         == read($PreCallHeap#2, q#0, _module.Node.val);
    assume q#0 != null
         && q#0 != a#0
         && q#0 != b#0
         && q#0 != c#0
         && q#0 != d#0
         && q#0 != e#0
         && q#0 != f#0
       ==> read($Heap, q#0, _module.Node.tag)
         == read($PreCallHeap#2, q#0, _module.Node.tag);
    assume q#0 != null
         && q#0 != a#0
         && q#0 != b#0
         && q#0 != c#0
         && q#0 != d#0
         && q#0 != e#0
         && q#0 != f#0
       ==> read($Heap, q#0, _module.Node.score)
         == read($PreCallHeap#2, q#0, _module.Node.score);
    assume q#0 != null
         && q#0 != a#0
         && q#0 != b#0
         && q#0 != c#0
         && q#0 != d#0
         && q#0 != e#0
         && q#0 != f#0
       ==> read($Heap, q#0, _module.Node.rank)
         == read($PreCallHeap#2, q#0, _module.Node.rank);
    assume r#0 != null
         && r#0 != a#0
         && r#0 != b#0
         && r#0 != c#0
         && r#0 != d#0
         && r#0 != e#0
         && r#0 != f#0
       ==> read($Heap, r#0, _module.Node.val)
         == read($PreCallHeap#2, r#0, _module.Node.val);
    assume r#0 != null
         && r#0 != a#0
         && r#0 != b#0
         && r#0 != c#0
         && r#0 != d#0
         && r#0 != e#0
         && r#0 != f#0
       ==> read($Heap, r#0, _module.Node.tag)
         == read($PreCallHeap#2, r#0, _module.Node.tag);
    assume r#0 != null
         && r#0 != a#0
         && r#0 != b#0
         && r#0 != c#0
         && r#0 != d#0
         && r#0 != e#0
         && r#0 != f#0
       ==> read($Heap, r#0, _module.Node.score)
         == read($PreCallHeap#2, r#0, _module.Node.score);
    assume r#0 != null
         && r#0 != a#0
         && r#0 != b#0
         && r#0 != c#0
         && r#0 != d#0
         && r#0 != e#0
         && r#0 != f#0
       ==> read($Heap, r#0, _module.Node.rank)
         == read($PreCallHeap#2, r#0, _module.Node.rank);
    assume s#0 != null
         && s#0 != a#0
         && s#0 != b#0
         && s#0 != c#0
         && s#0 != d#0
         && s#0 != e#0
         && s#0 != f#0
       ==> read($Heap, s#0, _module.Node.val)
         == read($PreCallHeap#2, s#0, _module.Node.val);
    assume s#0 != null
         && s#0 != a#0
         && s#0 != b#0
         && s#0 != c#0
         && s#0 != d#0
         && s#0 != e#0
         && s#0 != f#0
       ==> read($Heap, s#0, _module.Node.tag)
         == read($PreCallHeap#2, s#0, _module.Node.tag);
    assume s#0 != null
         && s#0 != a#0
         && s#0 != b#0
         && s#0 != c#0
         && s#0 != d#0
         && s#0 != e#0
         && s#0 != f#0
       ==> read($Heap, s#0, _module.Node.score)
         == read($PreCallHeap#2, s#0, _module.Node.score);
    assume s#0 != null
         && s#0 != a#0
         && s#0 != b#0
         && s#0 != c#0
         && s#0 != d#0
         && s#0 != e#0
         && s#0 != f#0
       ==> read($Heap, s#0, _module.Node.rank)
         == read($PreCallHeap#2, s#0, _module.Node.rank);
    assume t#0 != null
         && t#0 != a#0
         && t#0 != b#0
         && t#0 != c#0
         && t#0 != d#0
         && t#0 != e#0
         && t#0 != f#0
       ==> read($Heap, t#0, _module.Node.val)
         == read($PreCallHeap#2, t#0, _module.Node.val);
    assume t#0 != null
         && t#0 != a#0
         && t#0 != b#0
         && t#0 != c#0
         && t#0 != d#0
         && t#0 != e#0
         && t#0 != f#0
       ==> read($Heap, t#0, _module.Node.tag)
         == read($PreCallHeap#2, t#0, _module.Node.tag);
    assume t#0 != null
         && t#0 != a#0
         && t#0 != b#0
         && t#0 != c#0
         && t#0 != d#0
         && t#0 != e#0
         && t#0 != f#0
       ==> read($Heap, t#0, _module.Node.score)
         == read($PreCallHeap#2, t#0, _module.Node.score);
    assume t#0 != null
         && t#0 != a#0
         && t#0 != b#0
         && t#0 != c#0
         && t#0 != d#0
         && t#0 != e#0
         && t#0 != f#0
       ==> read($Heap, t#0, _module.Node.rank)
         == read($PreCallHeap#2, t#0, _module.Node.rank);
    assume u#0 != null
         && u#0 != a#0
         && u#0 != b#0
         && u#0 != c#0
         && u#0 != d#0
         && u#0 != e#0
         && u#0 != f#0
       ==> read($Heap, u#0, _module.Node.val)
         == read($PreCallHeap#2, u#0, _module.Node.val);
    assume u#0 != null
         && u#0 != a#0
         && u#0 != b#0
         && u#0 != c#0
         && u#0 != d#0
         && u#0 != e#0
         && u#0 != f#0
       ==> read($Heap, u#0, _module.Node.tag)
         == read($PreCallHeap#2, u#0, _module.Node.tag);
    assume u#0 != null
         && u#0 != a#0
         && u#0 != b#0
         && u#0 != c#0
         && u#0 != d#0
         && u#0 != e#0
         && u#0 != f#0
       ==> read($Heap, u#0, _module.Node.score)
         == read($PreCallHeap#2, u#0, _module.Node.score);
    assume u#0 != null
         && u#0 != a#0
         && u#0 != b#0
         && u#0 != c#0
         && u#0 != d#0
         && u#0 != e#0
         && u#0 != f#0
       ==> read($Heap, u#0, _module.Node.rank)
         == read($PreCallHeap#2, u#0, _module.Node.rank);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.val)
         == read($PreCallHeap#2, a##0, _module.Node.val);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.tag)
         == read($PreCallHeap#2, a##0, _module.Node.tag);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.score)
         == read($PreCallHeap#2, a##0, _module.Node.score);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != d#0
         && a##0 != e#0
         && a##0 != f#0
       ==> read($Heap, a##0, _module.Node.rank)
         == read($PreCallHeap#2, a##0, _module.Node.rank);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.val)
         == read($PreCallHeap#2, b##0, _module.Node.val);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.tag)
         == read($PreCallHeap#2, b##0, _module.Node.tag);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.score)
         == read($PreCallHeap#2, b##0, _module.Node.score);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != d#0
         && b##0 != e#0
         && b##0 != f#0
       ==> read($Heap, b##0, _module.Node.rank)
         == read($PreCallHeap#2, b##0, _module.Node.rank);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.val)
         == read($PreCallHeap#2, c##0, _module.Node.val);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.tag)
         == read($PreCallHeap#2, c##0, _module.Node.tag);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.score)
         == read($PreCallHeap#2, c##0, _module.Node.score);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != d#0
         && c##0 != e#0
         && c##0 != f#0
       ==> read($Heap, c##0, _module.Node.rank)
         == read($PreCallHeap#2, c##0, _module.Node.rank);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.val)
         == read($PreCallHeap#2, d##0, _module.Node.val);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.tag)
         == read($PreCallHeap#2, d##0, _module.Node.tag);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.score)
         == read($PreCallHeap#2, d##0, _module.Node.score);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != d#0
         && d##0 != e#0
         && d##0 != f#0
       ==> read($Heap, d##0, _module.Node.rank)
         == read($PreCallHeap#2, d##0, _module.Node.rank);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.val)
         == read($PreCallHeap#2, e##0, _module.Node.val);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.tag)
         == read($PreCallHeap#2, e##0, _module.Node.tag);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.score)
         == read($PreCallHeap#2, e##0, _module.Node.score);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != d#0
         && e##0 != e#0
         && e##0 != f#0
       ==> read($Heap, e##0, _module.Node.rank)
         == read($PreCallHeap#2, e##0, _module.Node.rank);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.val)
         == read($PreCallHeap#2, f##0, _module.Node.val);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.tag)
         == read($PreCallHeap#2, f##0, _module.Node.tag);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.score)
         == read($PreCallHeap#2, f##0, _module.Node.score);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != d#0
         && f##0 != e#0
         && f##0 != f#0
       ==> read($Heap, f##0, _module.Node.rank)
         == read($PreCallHeap#2, f##0, _module.Node.rank);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.val)
         == read($PreCallHeap#2, a##1, _module.Node.val);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.tag)
         == read($PreCallHeap#2, a##1, _module.Node.tag);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.score)
         == read($PreCallHeap#2, a##1, _module.Node.score);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != d#0
         && a##1 != e#0
         && a##1 != f#0
       ==> read($Heap, a##1, _module.Node.rank)
         == read($PreCallHeap#2, a##1, _module.Node.rank);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.val)
         == read($PreCallHeap#2, b##1, _module.Node.val);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.tag)
         == read($PreCallHeap#2, b##1, _module.Node.tag);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.score)
         == read($PreCallHeap#2, b##1, _module.Node.score);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != d#0
         && b##1 != e#0
         && b##1 != f#0
       ==> read($Heap, b##1, _module.Node.rank)
         == read($PreCallHeap#2, b##1, _module.Node.rank);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.val)
         == read($PreCallHeap#2, c##1, _module.Node.val);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.tag)
         == read($PreCallHeap#2, c##1, _module.Node.tag);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.score)
         == read($PreCallHeap#2, c##1, _module.Node.score);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != d#0
         && c##1 != e#0
         && c##1 != f#0
       ==> read($Heap, c##1, _module.Node.rank)
         == read($PreCallHeap#2, c##1, _module.Node.rank);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.val)
         == read($PreCallHeap#2, d##1, _module.Node.val);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.tag)
         == read($PreCallHeap#2, d##1, _module.Node.tag);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.score)
         == read($PreCallHeap#2, d##1, _module.Node.score);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != d#0
         && d##1 != e#0
         && d##1 != f#0
       ==> read($Heap, d##1, _module.Node.rank)
         == read($PreCallHeap#2, d##1, _module.Node.rank);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.val)
         == read($PreCallHeap#2, e##1, _module.Node.val);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.tag)
         == read($PreCallHeap#2, e##1, _module.Node.tag);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.score)
         == read($PreCallHeap#2, e##1, _module.Node.score);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != d#0
         && e##1 != e#0
         && e##1 != f#0
       ==> read($Heap, e##1, _module.Node.rank)
         == read($PreCallHeap#2, e##1, _module.Node.rank);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.val)
         == read($PreCallHeap#2, f##1, _module.Node.val);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.tag)
         == read($PreCallHeap#2, f##1, _module.Node.tag);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.score)
         == read($PreCallHeap#2, f##1, _module.Node.score);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != d#0
         && f##1 != e#0
         && f##1 != f#0
       ==> read($Heap, f##1, _module.Node.rank)
         == read($PreCallHeap#2, f##1, _module.Node.rank);
    assume a##2 != null
         && a##2 != a#0
         && a##2 != b#0
         && a##2 != c#0
         && a##2 != d#0
         && a##2 != e#0
         && a##2 != f#0
       ==> read($Heap, a##2, _module.Node.val)
         == read($PreCallHeap#2, a##2, _module.Node.val);
    assume a##2 != null
         && a##2 != a#0
         && a##2 != b#0
         && a##2 != c#0
         && a##2 != d#0
         && a##2 != e#0
         && a##2 != f#0
       ==> read($Heap, a##2, _module.Node.tag)
         == read($PreCallHeap#2, a##2, _module.Node.tag);
    assume a##2 != null
         && a##2 != a#0
         && a##2 != b#0
         && a##2 != c#0
         && a##2 != d#0
         && a##2 != e#0
         && a##2 != f#0
       ==> read($Heap, a##2, _module.Node.score)
         == read($PreCallHeap#2, a##2, _module.Node.score);
    assume a##2 != null
         && a##2 != a#0
         && a##2 != b#0
         && a##2 != c#0
         && a##2 != d#0
         && a##2 != e#0
         && a##2 != f#0
       ==> read($Heap, a##2, _module.Node.rank)
         == read($PreCallHeap#2, a##2, _module.Node.rank);
    assume b##2 != null
         && b##2 != a#0
         && b##2 != b#0
         && b##2 != c#0
         && b##2 != d#0
         && b##2 != e#0
         && b##2 != f#0
       ==> read($Heap, b##2, _module.Node.val)
         == read($PreCallHeap#2, b##2, _module.Node.val);
    assume b##2 != null
         && b##2 != a#0
         && b##2 != b#0
         && b##2 != c#0
         && b##2 != d#0
         && b##2 != e#0
         && b##2 != f#0
       ==> read($Heap, b##2, _module.Node.tag)
         == read($PreCallHeap#2, b##2, _module.Node.tag);
    assume b##2 != null
         && b##2 != a#0
         && b##2 != b#0
         && b##2 != c#0
         && b##2 != d#0
         && b##2 != e#0
         && b##2 != f#0
       ==> read($Heap, b##2, _module.Node.score)
         == read($PreCallHeap#2, b##2, _module.Node.score);
    assume b##2 != null
         && b##2 != a#0
         && b##2 != b#0
         && b##2 != c#0
         && b##2 != d#0
         && b##2 != e#0
         && b##2 != f#0
       ==> read($Heap, b##2, _module.Node.rank)
         == read($PreCallHeap#2, b##2, _module.Node.rank);
    assume c##2 != null
         && c##2 != a#0
         && c##2 != b#0
         && c##2 != c#0
         && c##2 != d#0
         && c##2 != e#0
         && c##2 != f#0
       ==> read($Heap, c##2, _module.Node.val)
         == read($PreCallHeap#2, c##2, _module.Node.val);
    assume c##2 != null
         && c##2 != a#0
         && c##2 != b#0
         && c##2 != c#0
         && c##2 != d#0
         && c##2 != e#0
         && c##2 != f#0
       ==> read($Heap, c##2, _module.Node.tag)
         == read($PreCallHeap#2, c##2, _module.Node.tag);
    assume c##2 != null
         && c##2 != a#0
         && c##2 != b#0
         && c##2 != c#0
         && c##2 != d#0
         && c##2 != e#0
         && c##2 != f#0
       ==> read($Heap, c##2, _module.Node.score)
         == read($PreCallHeap#2, c##2, _module.Node.score);
    assume c##2 != null
         && c##2 != a#0
         && c##2 != b#0
         && c##2 != c#0
         && c##2 != d#0
         && c##2 != e#0
         && c##2 != f#0
       ==> read($Heap, c##2, _module.Node.rank)
         == read($PreCallHeap#2, c##2, _module.Node.rank);
    assume d##2 != null
         && d##2 != a#0
         && d##2 != b#0
         && d##2 != c#0
         && d##2 != d#0
         && d##2 != e#0
         && d##2 != f#0
       ==> read($Heap, d##2, _module.Node.val)
         == read($PreCallHeap#2, d##2, _module.Node.val);
    assume d##2 != null
         && d##2 != a#0
         && d##2 != b#0
         && d##2 != c#0
         && d##2 != d#0
         && d##2 != e#0
         && d##2 != f#0
       ==> read($Heap, d##2, _module.Node.tag)
         == read($PreCallHeap#2, d##2, _module.Node.tag);
    assume d##2 != null
         && d##2 != a#0
         && d##2 != b#0
         && d##2 != c#0
         && d##2 != d#0
         && d##2 != e#0
         && d##2 != f#0
       ==> read($Heap, d##2, _module.Node.score)
         == read($PreCallHeap#2, d##2, _module.Node.score);
    assume d##2 != null
         && d##2 != a#0
         && d##2 != b#0
         && d##2 != c#0
         && d##2 != d#0
         && d##2 != e#0
         && d##2 != f#0
       ==> read($Heap, d##2, _module.Node.rank)
         == read($PreCallHeap#2, d##2, _module.Node.rank);
    assume e##2 != null
         && e##2 != a#0
         && e##2 != b#0
         && e##2 != c#0
         && e##2 != d#0
         && e##2 != e#0
         && e##2 != f#0
       ==> read($Heap, e##2, _module.Node.val)
         == read($PreCallHeap#2, e##2, _module.Node.val);
    assume e##2 != null
         && e##2 != a#0
         && e##2 != b#0
         && e##2 != c#0
         && e##2 != d#0
         && e##2 != e#0
         && e##2 != f#0
       ==> read($Heap, e##2, _module.Node.tag)
         == read($PreCallHeap#2, e##2, _module.Node.tag);
    assume e##2 != null
         && e##2 != a#0
         && e##2 != b#0
         && e##2 != c#0
         && e##2 != d#0
         && e##2 != e#0
         && e##2 != f#0
       ==> read($Heap, e##2, _module.Node.score)
         == read($PreCallHeap#2, e##2, _module.Node.score);
    assume e##2 != null
         && e##2 != a#0
         && e##2 != b#0
         && e##2 != c#0
         && e##2 != d#0
         && e##2 != e#0
         && e##2 != f#0
       ==> read($Heap, e##2, _module.Node.rank)
         == read($PreCallHeap#2, e##2, _module.Node.rank);
    assume f##2 != null
         && f##2 != a#0
         && f##2 != b#0
         && f##2 != c#0
         && f##2 != d#0
         && f##2 != e#0
         && f##2 != f#0
       ==> read($Heap, f##2, _module.Node.val)
         == read($PreCallHeap#2, f##2, _module.Node.val);
    assume f##2 != null
         && f##2 != a#0
         && f##2 != b#0
         && f##2 != c#0
         && f##2 != d#0
         && f##2 != e#0
         && f##2 != f#0
       ==> read($Heap, f##2, _module.Node.tag)
         == read($PreCallHeap#2, f##2, _module.Node.tag);
    assume f##2 != null
         && f##2 != a#0
         && f##2 != b#0
         && f##2 != c#0
         && f##2 != d#0
         && f##2 != e#0
         && f##2 != f#0
       ==> read($Heap, f##2, _module.Node.score)
         == read($PreCallHeap#2, f##2, _module.Node.score);
    assume f##2 != null
         && f##2 != a#0
         && f##2 != b#0
         && f##2 != c#0
         && f##2 != d#0
         && f##2 != e#0
         && f##2 != f#0
       ==> read($Heap, f##2, _module.Node.rank)
         == read($PreCallHeap#2, f##2, _module.Node.rank);
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
    $PreCallHeap#3 := $Heap;
    $PreCallAlloc#3 := $Alloc;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id2164"} a##3 == a#0
       || a##3 == b#0
       || a##3 == c#0
       || a##3 == d#0
       || a##3 == e#0
       || a##3 == f#0
       || a##3 == p#0
       || a##3 == q#0
       || a##3 == r#0
       || a##3 == s#0
       || a##3 == t#0
       || a##3 == u#0
       || !old($Alloc)[a##3];
    assert {:id "id2165"} b##3 == a#0
       || b##3 == b#0
       || b##3 == c#0
       || b##3 == d#0
       || b##3 == e#0
       || b##3 == f#0
       || b##3 == p#0
       || b##3 == q#0
       || b##3 == r#0
       || b##3 == s#0
       || b##3 == t#0
       || b##3 == u#0
       || !old($Alloc)[b##3];
    assert {:id "id2166"} c##3 == a#0
       || c##3 == b#0
       || c##3 == c#0
       || c##3 == d#0
       || c##3 == e#0
       || c##3 == f#0
       || c##3 == p#0
       || c##3 == q#0
       || c##3 == r#0
       || c##3 == s#0
       || c##3 == t#0
       || c##3 == u#0
       || !old($Alloc)[c##3];
    assert {:id "id2167"} p##0 == a#0
       || p##0 == b#0
       || p##0 == c#0
       || p##0 == d#0
       || p##0 == e#0
       || p##0 == f#0
       || p##0 == p#0
       || p##0 == q#0
       || p##0 == r#0
       || p##0 == s#0
       || p##0 == t#0
       || p##0 == u#0
       || !old($Alloc)[p##0];
    assert {:id "id2168"} q##0 == a#0
       || q##0 == b#0
       || q##0 == c#0
       || q##0 == d#0
       || q##0 == e#0
       || q##0 == f#0
       || q##0 == p#0
       || q##0 == q#0
       || q##0 == r#0
       || q##0 == s#0
       || q##0 == t#0
       || q##0 == u#0
       || !old($Alloc)[q##0];
    assert {:id "id2169"} r##0 == a#0
       || r##0 == b#0
       || r##0 == c#0
       || r##0 == d#0
       || r##0 == e#0
       || r##0 == f#0
       || r##0 == p#0
       || r##0 == q#0
       || r##0 == r#0
       || r##0 == s#0
       || r##0 == t#0
       || r##0 == u#0
       || !old($Alloc)[r##0];
    call {:id "id2170"} Call$$_module.__default.CrossBump(a##3, b##3, c##3, p##0, q##0, r##0);
    // qf-call-frame CrossBump: supports=36 reads=144 modified=6
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != p#0
         && a#0 != q#0
         && a#0 != r#0
       ==> read($Heap, a#0, _module.Node.val)
         == read($PreCallHeap#3, a#0, _module.Node.val);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != p#0
         && a#0 != q#0
         && a#0 != r#0
       ==> read($Heap, a#0, _module.Node.tag)
         == read($PreCallHeap#3, a#0, _module.Node.tag);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != p#0
         && a#0 != q#0
         && a#0 != r#0
       ==> read($Heap, a#0, _module.Node.score)
         == read($PreCallHeap#3, a#0, _module.Node.score);
    assume a#0 != null
         && a#0 != a#0
         && a#0 != b#0
         && a#0 != c#0
         && a#0 != p#0
         && a#0 != q#0
         && a#0 != r#0
       ==> read($Heap, a#0, _module.Node.rank)
         == read($PreCallHeap#3, a#0, _module.Node.rank);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != p#0
         && b#0 != q#0
         && b#0 != r#0
       ==> read($Heap, b#0, _module.Node.val)
         == read($PreCallHeap#3, b#0, _module.Node.val);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != p#0
         && b#0 != q#0
         && b#0 != r#0
       ==> read($Heap, b#0, _module.Node.tag)
         == read($PreCallHeap#3, b#0, _module.Node.tag);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != p#0
         && b#0 != q#0
         && b#0 != r#0
       ==> read($Heap, b#0, _module.Node.score)
         == read($PreCallHeap#3, b#0, _module.Node.score);
    assume b#0 != null
         && b#0 != a#0
         && b#0 != b#0
         && b#0 != c#0
         && b#0 != p#0
         && b#0 != q#0
         && b#0 != r#0
       ==> read($Heap, b#0, _module.Node.rank)
         == read($PreCallHeap#3, b#0, _module.Node.rank);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != p#0
         && c#0 != q#0
         && c#0 != r#0
       ==> read($Heap, c#0, _module.Node.val)
         == read($PreCallHeap#3, c#0, _module.Node.val);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != p#0
         && c#0 != q#0
         && c#0 != r#0
       ==> read($Heap, c#0, _module.Node.tag)
         == read($PreCallHeap#3, c#0, _module.Node.tag);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != p#0
         && c#0 != q#0
         && c#0 != r#0
       ==> read($Heap, c#0, _module.Node.score)
         == read($PreCallHeap#3, c#0, _module.Node.score);
    assume c#0 != null
         && c#0 != a#0
         && c#0 != b#0
         && c#0 != c#0
         && c#0 != p#0
         && c#0 != q#0
         && c#0 != r#0
       ==> read($Heap, c#0, _module.Node.rank)
         == read($PreCallHeap#3, c#0, _module.Node.rank);
    assume p#0 != null
         && p#0 != a#0
         && p#0 != b#0
         && p#0 != c#0
         && p#0 != p#0
         && p#0 != q#0
         && p#0 != r#0
       ==> read($Heap, p#0, _module.Node.val)
         == read($PreCallHeap#3, p#0, _module.Node.val);
    assume p#0 != null
         && p#0 != a#0
         && p#0 != b#0
         && p#0 != c#0
         && p#0 != p#0
         && p#0 != q#0
         && p#0 != r#0
       ==> read($Heap, p#0, _module.Node.tag)
         == read($PreCallHeap#3, p#0, _module.Node.tag);
    assume p#0 != null
         && p#0 != a#0
         && p#0 != b#0
         && p#0 != c#0
         && p#0 != p#0
         && p#0 != q#0
         && p#0 != r#0
       ==> read($Heap, p#0, _module.Node.score)
         == read($PreCallHeap#3, p#0, _module.Node.score);
    assume p#0 != null
         && p#0 != a#0
         && p#0 != b#0
         && p#0 != c#0
         && p#0 != p#0
         && p#0 != q#0
         && p#0 != r#0
       ==> read($Heap, p#0, _module.Node.rank)
         == read($PreCallHeap#3, p#0, _module.Node.rank);
    assume q#0 != null
         && q#0 != a#0
         && q#0 != b#0
         && q#0 != c#0
         && q#0 != p#0
         && q#0 != q#0
         && q#0 != r#0
       ==> read($Heap, q#0, _module.Node.val)
         == read($PreCallHeap#3, q#0, _module.Node.val);
    assume q#0 != null
         && q#0 != a#0
         && q#0 != b#0
         && q#0 != c#0
         && q#0 != p#0
         && q#0 != q#0
         && q#0 != r#0
       ==> read($Heap, q#0, _module.Node.tag)
         == read($PreCallHeap#3, q#0, _module.Node.tag);
    assume q#0 != null
         && q#0 != a#0
         && q#0 != b#0
         && q#0 != c#0
         && q#0 != p#0
         && q#0 != q#0
         && q#0 != r#0
       ==> read($Heap, q#0, _module.Node.score)
         == read($PreCallHeap#3, q#0, _module.Node.score);
    assume q#0 != null
         && q#0 != a#0
         && q#0 != b#0
         && q#0 != c#0
         && q#0 != p#0
         && q#0 != q#0
         && q#0 != r#0
       ==> read($Heap, q#0, _module.Node.rank)
         == read($PreCallHeap#3, q#0, _module.Node.rank);
    assume r#0 != null
         && r#0 != a#0
         && r#0 != b#0
         && r#0 != c#0
         && r#0 != p#0
         && r#0 != q#0
         && r#0 != r#0
       ==> read($Heap, r#0, _module.Node.val)
         == read($PreCallHeap#3, r#0, _module.Node.val);
    assume r#0 != null
         && r#0 != a#0
         && r#0 != b#0
         && r#0 != c#0
         && r#0 != p#0
         && r#0 != q#0
         && r#0 != r#0
       ==> read($Heap, r#0, _module.Node.tag)
         == read($PreCallHeap#3, r#0, _module.Node.tag);
    assume r#0 != null
         && r#0 != a#0
         && r#0 != b#0
         && r#0 != c#0
         && r#0 != p#0
         && r#0 != q#0
         && r#0 != r#0
       ==> read($Heap, r#0, _module.Node.score)
         == read($PreCallHeap#3, r#0, _module.Node.score);
    assume r#0 != null
         && r#0 != a#0
         && r#0 != b#0
         && r#0 != c#0
         && r#0 != p#0
         && r#0 != q#0
         && r#0 != r#0
       ==> read($Heap, r#0, _module.Node.rank)
         == read($PreCallHeap#3, r#0, _module.Node.rank);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != p#0
         && d#0 != q#0
         && d#0 != r#0
       ==> read($Heap, d#0, _module.Node.val)
         == read($PreCallHeap#3, d#0, _module.Node.val);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != p#0
         && d#0 != q#0
         && d#0 != r#0
       ==> read($Heap, d#0, _module.Node.tag)
         == read($PreCallHeap#3, d#0, _module.Node.tag);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != p#0
         && d#0 != q#0
         && d#0 != r#0
       ==> read($Heap, d#0, _module.Node.score)
         == read($PreCallHeap#3, d#0, _module.Node.score);
    assume d#0 != null
         && d#0 != a#0
         && d#0 != b#0
         && d#0 != c#0
         && d#0 != p#0
         && d#0 != q#0
         && d#0 != r#0
       ==> read($Heap, d#0, _module.Node.rank)
         == read($PreCallHeap#3, d#0, _module.Node.rank);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != p#0
         && e#0 != q#0
         && e#0 != r#0
       ==> read($Heap, e#0, _module.Node.val)
         == read($PreCallHeap#3, e#0, _module.Node.val);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != p#0
         && e#0 != q#0
         && e#0 != r#0
       ==> read($Heap, e#0, _module.Node.tag)
         == read($PreCallHeap#3, e#0, _module.Node.tag);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != p#0
         && e#0 != q#0
         && e#0 != r#0
       ==> read($Heap, e#0, _module.Node.score)
         == read($PreCallHeap#3, e#0, _module.Node.score);
    assume e#0 != null
         && e#0 != a#0
         && e#0 != b#0
         && e#0 != c#0
         && e#0 != p#0
         && e#0 != q#0
         && e#0 != r#0
       ==> read($Heap, e#0, _module.Node.rank)
         == read($PreCallHeap#3, e#0, _module.Node.rank);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != p#0
         && f#0 != q#0
         && f#0 != r#0
       ==> read($Heap, f#0, _module.Node.val)
         == read($PreCallHeap#3, f#0, _module.Node.val);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != p#0
         && f#0 != q#0
         && f#0 != r#0
       ==> read($Heap, f#0, _module.Node.tag)
         == read($PreCallHeap#3, f#0, _module.Node.tag);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != p#0
         && f#0 != q#0
         && f#0 != r#0
       ==> read($Heap, f#0, _module.Node.score)
         == read($PreCallHeap#3, f#0, _module.Node.score);
    assume f#0 != null
         && f#0 != a#0
         && f#0 != b#0
         && f#0 != c#0
         && f#0 != p#0
         && f#0 != q#0
         && f#0 != r#0
       ==> read($Heap, f#0, _module.Node.rank)
         == read($PreCallHeap#3, f#0, _module.Node.rank);
    assume s#0 != null
         && s#0 != a#0
         && s#0 != b#0
         && s#0 != c#0
         && s#0 != p#0
         && s#0 != q#0
         && s#0 != r#0
       ==> read($Heap, s#0, _module.Node.val)
         == read($PreCallHeap#3, s#0, _module.Node.val);
    assume s#0 != null
         && s#0 != a#0
         && s#0 != b#0
         && s#0 != c#0
         && s#0 != p#0
         && s#0 != q#0
         && s#0 != r#0
       ==> read($Heap, s#0, _module.Node.tag)
         == read($PreCallHeap#3, s#0, _module.Node.tag);
    assume s#0 != null
         && s#0 != a#0
         && s#0 != b#0
         && s#0 != c#0
         && s#0 != p#0
         && s#0 != q#0
         && s#0 != r#0
       ==> read($Heap, s#0, _module.Node.score)
         == read($PreCallHeap#3, s#0, _module.Node.score);
    assume s#0 != null
         && s#0 != a#0
         && s#0 != b#0
         && s#0 != c#0
         && s#0 != p#0
         && s#0 != q#0
         && s#0 != r#0
       ==> read($Heap, s#0, _module.Node.rank)
         == read($PreCallHeap#3, s#0, _module.Node.rank);
    assume t#0 != null
         && t#0 != a#0
         && t#0 != b#0
         && t#0 != c#0
         && t#0 != p#0
         && t#0 != q#0
         && t#0 != r#0
       ==> read($Heap, t#0, _module.Node.val)
         == read($PreCallHeap#3, t#0, _module.Node.val);
    assume t#0 != null
         && t#0 != a#0
         && t#0 != b#0
         && t#0 != c#0
         && t#0 != p#0
         && t#0 != q#0
         && t#0 != r#0
       ==> read($Heap, t#0, _module.Node.tag)
         == read($PreCallHeap#3, t#0, _module.Node.tag);
    assume t#0 != null
         && t#0 != a#0
         && t#0 != b#0
         && t#0 != c#0
         && t#0 != p#0
         && t#0 != q#0
         && t#0 != r#0
       ==> read($Heap, t#0, _module.Node.score)
         == read($PreCallHeap#3, t#0, _module.Node.score);
    assume t#0 != null
         && t#0 != a#0
         && t#0 != b#0
         && t#0 != c#0
         && t#0 != p#0
         && t#0 != q#0
         && t#0 != r#0
       ==> read($Heap, t#0, _module.Node.rank)
         == read($PreCallHeap#3, t#0, _module.Node.rank);
    assume u#0 != null
         && u#0 != a#0
         && u#0 != b#0
         && u#0 != c#0
         && u#0 != p#0
         && u#0 != q#0
         && u#0 != r#0
       ==> read($Heap, u#0, _module.Node.val)
         == read($PreCallHeap#3, u#0, _module.Node.val);
    assume u#0 != null
         && u#0 != a#0
         && u#0 != b#0
         && u#0 != c#0
         && u#0 != p#0
         && u#0 != q#0
         && u#0 != r#0
       ==> read($Heap, u#0, _module.Node.tag)
         == read($PreCallHeap#3, u#0, _module.Node.tag);
    assume u#0 != null
         && u#0 != a#0
         && u#0 != b#0
         && u#0 != c#0
         && u#0 != p#0
         && u#0 != q#0
         && u#0 != r#0
       ==> read($Heap, u#0, _module.Node.score)
         == read($PreCallHeap#3, u#0, _module.Node.score);
    assume u#0 != null
         && u#0 != a#0
         && u#0 != b#0
         && u#0 != c#0
         && u#0 != p#0
         && u#0 != q#0
         && u#0 != r#0
       ==> read($Heap, u#0, _module.Node.rank)
         == read($PreCallHeap#3, u#0, _module.Node.rank);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != p#0
         && a##0 != q#0
         && a##0 != r#0
       ==> read($Heap, a##0, _module.Node.val)
         == read($PreCallHeap#3, a##0, _module.Node.val);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != p#0
         && a##0 != q#0
         && a##0 != r#0
       ==> read($Heap, a##0, _module.Node.tag)
         == read($PreCallHeap#3, a##0, _module.Node.tag);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != p#0
         && a##0 != q#0
         && a##0 != r#0
       ==> read($Heap, a##0, _module.Node.score)
         == read($PreCallHeap#3, a##0, _module.Node.score);
    assume a##0 != null
         && a##0 != a#0
         && a##0 != b#0
         && a##0 != c#0
         && a##0 != p#0
         && a##0 != q#0
         && a##0 != r#0
       ==> read($Heap, a##0, _module.Node.rank)
         == read($PreCallHeap#3, a##0, _module.Node.rank);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != p#0
         && b##0 != q#0
         && b##0 != r#0
       ==> read($Heap, b##0, _module.Node.val)
         == read($PreCallHeap#3, b##0, _module.Node.val);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != p#0
         && b##0 != q#0
         && b##0 != r#0
       ==> read($Heap, b##0, _module.Node.tag)
         == read($PreCallHeap#3, b##0, _module.Node.tag);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != p#0
         && b##0 != q#0
         && b##0 != r#0
       ==> read($Heap, b##0, _module.Node.score)
         == read($PreCallHeap#3, b##0, _module.Node.score);
    assume b##0 != null
         && b##0 != a#0
         && b##0 != b#0
         && b##0 != c#0
         && b##0 != p#0
         && b##0 != q#0
         && b##0 != r#0
       ==> read($Heap, b##0, _module.Node.rank)
         == read($PreCallHeap#3, b##0, _module.Node.rank);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != p#0
         && c##0 != q#0
         && c##0 != r#0
       ==> read($Heap, c##0, _module.Node.val)
         == read($PreCallHeap#3, c##0, _module.Node.val);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != p#0
         && c##0 != q#0
         && c##0 != r#0
       ==> read($Heap, c##0, _module.Node.tag)
         == read($PreCallHeap#3, c##0, _module.Node.tag);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != p#0
         && c##0 != q#0
         && c##0 != r#0
       ==> read($Heap, c##0, _module.Node.score)
         == read($PreCallHeap#3, c##0, _module.Node.score);
    assume c##0 != null
         && c##0 != a#0
         && c##0 != b#0
         && c##0 != c#0
         && c##0 != p#0
         && c##0 != q#0
         && c##0 != r#0
       ==> read($Heap, c##0, _module.Node.rank)
         == read($PreCallHeap#3, c##0, _module.Node.rank);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != p#0
         && d##0 != q#0
         && d##0 != r#0
       ==> read($Heap, d##0, _module.Node.val)
         == read($PreCallHeap#3, d##0, _module.Node.val);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != p#0
         && d##0 != q#0
         && d##0 != r#0
       ==> read($Heap, d##0, _module.Node.tag)
         == read($PreCallHeap#3, d##0, _module.Node.tag);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != p#0
         && d##0 != q#0
         && d##0 != r#0
       ==> read($Heap, d##0, _module.Node.score)
         == read($PreCallHeap#3, d##0, _module.Node.score);
    assume d##0 != null
         && d##0 != a#0
         && d##0 != b#0
         && d##0 != c#0
         && d##0 != p#0
         && d##0 != q#0
         && d##0 != r#0
       ==> read($Heap, d##0, _module.Node.rank)
         == read($PreCallHeap#3, d##0, _module.Node.rank);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != p#0
         && e##0 != q#0
         && e##0 != r#0
       ==> read($Heap, e##0, _module.Node.val)
         == read($PreCallHeap#3, e##0, _module.Node.val);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != p#0
         && e##0 != q#0
         && e##0 != r#0
       ==> read($Heap, e##0, _module.Node.tag)
         == read($PreCallHeap#3, e##0, _module.Node.tag);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != p#0
         && e##0 != q#0
         && e##0 != r#0
       ==> read($Heap, e##0, _module.Node.score)
         == read($PreCallHeap#3, e##0, _module.Node.score);
    assume e##0 != null
         && e##0 != a#0
         && e##0 != b#0
         && e##0 != c#0
         && e##0 != p#0
         && e##0 != q#0
         && e##0 != r#0
       ==> read($Heap, e##0, _module.Node.rank)
         == read($PreCallHeap#3, e##0, _module.Node.rank);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != p#0
         && f##0 != q#0
         && f##0 != r#0
       ==> read($Heap, f##0, _module.Node.val)
         == read($PreCallHeap#3, f##0, _module.Node.val);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != p#0
         && f##0 != q#0
         && f##0 != r#0
       ==> read($Heap, f##0, _module.Node.tag)
         == read($PreCallHeap#3, f##0, _module.Node.tag);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != p#0
         && f##0 != q#0
         && f##0 != r#0
       ==> read($Heap, f##0, _module.Node.score)
         == read($PreCallHeap#3, f##0, _module.Node.score);
    assume f##0 != null
         && f##0 != a#0
         && f##0 != b#0
         && f##0 != c#0
         && f##0 != p#0
         && f##0 != q#0
         && f##0 != r#0
       ==> read($Heap, f##0, _module.Node.rank)
         == read($PreCallHeap#3, f##0, _module.Node.rank);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != p#0
         && a##1 != q#0
         && a##1 != r#0
       ==> read($Heap, a##1, _module.Node.val)
         == read($PreCallHeap#3, a##1, _module.Node.val);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != p#0
         && a##1 != q#0
         && a##1 != r#0
       ==> read($Heap, a##1, _module.Node.tag)
         == read($PreCallHeap#3, a##1, _module.Node.tag);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != p#0
         && a##1 != q#0
         && a##1 != r#0
       ==> read($Heap, a##1, _module.Node.score)
         == read($PreCallHeap#3, a##1, _module.Node.score);
    assume a##1 != null
         && a##1 != a#0
         && a##1 != b#0
         && a##1 != c#0
         && a##1 != p#0
         && a##1 != q#0
         && a##1 != r#0
       ==> read($Heap, a##1, _module.Node.rank)
         == read($PreCallHeap#3, a##1, _module.Node.rank);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != p#0
         && b##1 != q#0
         && b##1 != r#0
       ==> read($Heap, b##1, _module.Node.val)
         == read($PreCallHeap#3, b##1, _module.Node.val);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != p#0
         && b##1 != q#0
         && b##1 != r#0
       ==> read($Heap, b##1, _module.Node.tag)
         == read($PreCallHeap#3, b##1, _module.Node.tag);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != p#0
         && b##1 != q#0
         && b##1 != r#0
       ==> read($Heap, b##1, _module.Node.score)
         == read($PreCallHeap#3, b##1, _module.Node.score);
    assume b##1 != null
         && b##1 != a#0
         && b##1 != b#0
         && b##1 != c#0
         && b##1 != p#0
         && b##1 != q#0
         && b##1 != r#0
       ==> read($Heap, b##1, _module.Node.rank)
         == read($PreCallHeap#3, b##1, _module.Node.rank);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != p#0
         && c##1 != q#0
         && c##1 != r#0
       ==> read($Heap, c##1, _module.Node.val)
         == read($PreCallHeap#3, c##1, _module.Node.val);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != p#0
         && c##1 != q#0
         && c##1 != r#0
       ==> read($Heap, c##1, _module.Node.tag)
         == read($PreCallHeap#3, c##1, _module.Node.tag);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != p#0
         && c##1 != q#0
         && c##1 != r#0
       ==> read($Heap, c##1, _module.Node.score)
         == read($PreCallHeap#3, c##1, _module.Node.score);
    assume c##1 != null
         && c##1 != a#0
         && c##1 != b#0
         && c##1 != c#0
         && c##1 != p#0
         && c##1 != q#0
         && c##1 != r#0
       ==> read($Heap, c##1, _module.Node.rank)
         == read($PreCallHeap#3, c##1, _module.Node.rank);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != p#0
         && d##1 != q#0
         && d##1 != r#0
       ==> read($Heap, d##1, _module.Node.val)
         == read($PreCallHeap#3, d##1, _module.Node.val);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != p#0
         && d##1 != q#0
         && d##1 != r#0
       ==> read($Heap, d##1, _module.Node.tag)
         == read($PreCallHeap#3, d##1, _module.Node.tag);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != p#0
         && d##1 != q#0
         && d##1 != r#0
       ==> read($Heap, d##1, _module.Node.score)
         == read($PreCallHeap#3, d##1, _module.Node.score);
    assume d##1 != null
         && d##1 != a#0
         && d##1 != b#0
         && d##1 != c#0
         && d##1 != p#0
         && d##1 != q#0
         && d##1 != r#0
       ==> read($Heap, d##1, _module.Node.rank)
         == read($PreCallHeap#3, d##1, _module.Node.rank);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != p#0
         && e##1 != q#0
         && e##1 != r#0
       ==> read($Heap, e##1, _module.Node.val)
         == read($PreCallHeap#3, e##1, _module.Node.val);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != p#0
         && e##1 != q#0
         && e##1 != r#0
       ==> read($Heap, e##1, _module.Node.tag)
         == read($PreCallHeap#3, e##1, _module.Node.tag);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != p#0
         && e##1 != q#0
         && e##1 != r#0
       ==> read($Heap, e##1, _module.Node.score)
         == read($PreCallHeap#3, e##1, _module.Node.score);
    assume e##1 != null
         && e##1 != a#0
         && e##1 != b#0
         && e##1 != c#0
         && e##1 != p#0
         && e##1 != q#0
         && e##1 != r#0
       ==> read($Heap, e##1, _module.Node.rank)
         == read($PreCallHeap#3, e##1, _module.Node.rank);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != p#0
         && f##1 != q#0
         && f##1 != r#0
       ==> read($Heap, f##1, _module.Node.val)
         == read($PreCallHeap#3, f##1, _module.Node.val);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != p#0
         && f##1 != q#0
         && f##1 != r#0
       ==> read($Heap, f##1, _module.Node.tag)
         == read($PreCallHeap#3, f##1, _module.Node.tag);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != p#0
         && f##1 != q#0
         && f##1 != r#0
       ==> read($Heap, f##1, _module.Node.score)
         == read($PreCallHeap#3, f##1, _module.Node.score);
    assume f##1 != null
         && f##1 != a#0
         && f##1 != b#0
         && f##1 != c#0
         && f##1 != p#0
         && f##1 != q#0
         && f##1 != r#0
       ==> read($Heap, f##1, _module.Node.rank)
         == read($PreCallHeap#3, f##1, _module.Node.rank);
    assume a##2 != null
         && a##2 != a#0
         && a##2 != b#0
         && a##2 != c#0
         && a##2 != p#0
         && a##2 != q#0
         && a##2 != r#0
       ==> read($Heap, a##2, _module.Node.val)
         == read($PreCallHeap#3, a##2, _module.Node.val);
    assume a##2 != null
         && a##2 != a#0
         && a##2 != b#0
         && a##2 != c#0
         && a##2 != p#0
         && a##2 != q#0
         && a##2 != r#0
       ==> read($Heap, a##2, _module.Node.tag)
         == read($PreCallHeap#3, a##2, _module.Node.tag);
    assume a##2 != null
         && a##2 != a#0
         && a##2 != b#0
         && a##2 != c#0
         && a##2 != p#0
         && a##2 != q#0
         && a##2 != r#0
       ==> read($Heap, a##2, _module.Node.score)
         == read($PreCallHeap#3, a##2, _module.Node.score);
    assume a##2 != null
         && a##2 != a#0
         && a##2 != b#0
         && a##2 != c#0
         && a##2 != p#0
         && a##2 != q#0
         && a##2 != r#0
       ==> read($Heap, a##2, _module.Node.rank)
         == read($PreCallHeap#3, a##2, _module.Node.rank);
    assume b##2 != null
         && b##2 != a#0
         && b##2 != b#0
         && b##2 != c#0
         && b##2 != p#0
         && b##2 != q#0
         && b##2 != r#0
       ==> read($Heap, b##2, _module.Node.val)
         == read($PreCallHeap#3, b##2, _module.Node.val);
    assume b##2 != null
         && b##2 != a#0
         && b##2 != b#0
         && b##2 != c#0
         && b##2 != p#0
         && b##2 != q#0
         && b##2 != r#0
       ==> read($Heap, b##2, _module.Node.tag)
         == read($PreCallHeap#3, b##2, _module.Node.tag);
    assume b##2 != null
         && b##2 != a#0
         && b##2 != b#0
         && b##2 != c#0
         && b##2 != p#0
         && b##2 != q#0
         && b##2 != r#0
       ==> read($Heap, b##2, _module.Node.score)
         == read($PreCallHeap#3, b##2, _module.Node.score);
    assume b##2 != null
         && b##2 != a#0
         && b##2 != b#0
         && b##2 != c#0
         && b##2 != p#0
         && b##2 != q#0
         && b##2 != r#0
       ==> read($Heap, b##2, _module.Node.rank)
         == read($PreCallHeap#3, b##2, _module.Node.rank);
    assume c##2 != null
         && c##2 != a#0
         && c##2 != b#0
         && c##2 != c#0
         && c##2 != p#0
         && c##2 != q#0
         && c##2 != r#0
       ==> read($Heap, c##2, _module.Node.val)
         == read($PreCallHeap#3, c##2, _module.Node.val);
    assume c##2 != null
         && c##2 != a#0
         && c##2 != b#0
         && c##2 != c#0
         && c##2 != p#0
         && c##2 != q#0
         && c##2 != r#0
       ==> read($Heap, c##2, _module.Node.tag)
         == read($PreCallHeap#3, c##2, _module.Node.tag);
    assume c##2 != null
         && c##2 != a#0
         && c##2 != b#0
         && c##2 != c#0
         && c##2 != p#0
         && c##2 != q#0
         && c##2 != r#0
       ==> read($Heap, c##2, _module.Node.score)
         == read($PreCallHeap#3, c##2, _module.Node.score);
    assume c##2 != null
         && c##2 != a#0
         && c##2 != b#0
         && c##2 != c#0
         && c##2 != p#0
         && c##2 != q#0
         && c##2 != r#0
       ==> read($Heap, c##2, _module.Node.rank)
         == read($PreCallHeap#3, c##2, _module.Node.rank);
    assume d##2 != null
         && d##2 != a#0
         && d##2 != b#0
         && d##2 != c#0
         && d##2 != p#0
         && d##2 != q#0
         && d##2 != r#0
       ==> read($Heap, d##2, _module.Node.val)
         == read($PreCallHeap#3, d##2, _module.Node.val);
    assume d##2 != null
         && d##2 != a#0
         && d##2 != b#0
         && d##2 != c#0
         && d##2 != p#0
         && d##2 != q#0
         && d##2 != r#0
       ==> read($Heap, d##2, _module.Node.tag)
         == read($PreCallHeap#3, d##2, _module.Node.tag);
    assume d##2 != null
         && d##2 != a#0
         && d##2 != b#0
         && d##2 != c#0
         && d##2 != p#0
         && d##2 != q#0
         && d##2 != r#0
       ==> read($Heap, d##2, _module.Node.score)
         == read($PreCallHeap#3, d##2, _module.Node.score);
    assume d##2 != null
         && d##2 != a#0
         && d##2 != b#0
         && d##2 != c#0
         && d##2 != p#0
         && d##2 != q#0
         && d##2 != r#0
       ==> read($Heap, d##2, _module.Node.rank)
         == read($PreCallHeap#3, d##2, _module.Node.rank);
    assume e##2 != null
         && e##2 != a#0
         && e##2 != b#0
         && e##2 != c#0
         && e##2 != p#0
         && e##2 != q#0
         && e##2 != r#0
       ==> read($Heap, e##2, _module.Node.val)
         == read($PreCallHeap#3, e##2, _module.Node.val);
    assume e##2 != null
         && e##2 != a#0
         && e##2 != b#0
         && e##2 != c#0
         && e##2 != p#0
         && e##2 != q#0
         && e##2 != r#0
       ==> read($Heap, e##2, _module.Node.tag)
         == read($PreCallHeap#3, e##2, _module.Node.tag);
    assume e##2 != null
         && e##2 != a#0
         && e##2 != b#0
         && e##2 != c#0
         && e##2 != p#0
         && e##2 != q#0
         && e##2 != r#0
       ==> read($Heap, e##2, _module.Node.score)
         == read($PreCallHeap#3, e##2, _module.Node.score);
    assume e##2 != null
         && e##2 != a#0
         && e##2 != b#0
         && e##2 != c#0
         && e##2 != p#0
         && e##2 != q#0
         && e##2 != r#0
       ==> read($Heap, e##2, _module.Node.rank)
         == read($PreCallHeap#3, e##2, _module.Node.rank);
    assume f##2 != null
         && f##2 != a#0
         && f##2 != b#0
         && f##2 != c#0
         && f##2 != p#0
         && f##2 != q#0
         && f##2 != r#0
       ==> read($Heap, f##2, _module.Node.val)
         == read($PreCallHeap#3, f##2, _module.Node.val);
    assume f##2 != null
         && f##2 != a#0
         && f##2 != b#0
         && f##2 != c#0
         && f##2 != p#0
         && f##2 != q#0
         && f##2 != r#0
       ==> read($Heap, f##2, _module.Node.tag)
         == read($PreCallHeap#3, f##2, _module.Node.tag);
    assume f##2 != null
         && f##2 != a#0
         && f##2 != b#0
         && f##2 != c#0
         && f##2 != p#0
         && f##2 != q#0
         && f##2 != r#0
       ==> read($Heap, f##2, _module.Node.score)
         == read($PreCallHeap#3, f##2, _module.Node.score);
    assume f##2 != null
         && f##2 != a#0
         && f##2 != b#0
         && f##2 != c#0
         && f##2 != p#0
         && f##2 != q#0
         && f##2 != r#0
       ==> read($Heap, f##2, _module.Node.rank)
         == read($PreCallHeap#3, f##2, _module.Node.rank);
    assume a##3 != null
         && a##3 != a#0
         && a##3 != b#0
         && a##3 != c#0
         && a##3 != p#0
         && a##3 != q#0
         && a##3 != r#0
       ==> read($Heap, a##3, _module.Node.val)
         == read($PreCallHeap#3, a##3, _module.Node.val);
    assume a##3 != null
         && a##3 != a#0
         && a##3 != b#0
         && a##3 != c#0
         && a##3 != p#0
         && a##3 != q#0
         && a##3 != r#0
       ==> read($Heap, a##3, _module.Node.tag)
         == read($PreCallHeap#3, a##3, _module.Node.tag);
    assume a##3 != null
         && a##3 != a#0
         && a##3 != b#0
         && a##3 != c#0
         && a##3 != p#0
         && a##3 != q#0
         && a##3 != r#0
       ==> read($Heap, a##3, _module.Node.score)
         == read($PreCallHeap#3, a##3, _module.Node.score);
    assume a##3 != null
         && a##3 != a#0
         && a##3 != b#0
         && a##3 != c#0
         && a##3 != p#0
         && a##3 != q#0
         && a##3 != r#0
       ==> read($Heap, a##3, _module.Node.rank)
         == read($PreCallHeap#3, a##3, _module.Node.rank);
    assume b##3 != null
         && b##3 != a#0
         && b##3 != b#0
         && b##3 != c#0
         && b##3 != p#0
         && b##3 != q#0
         && b##3 != r#0
       ==> read($Heap, b##3, _module.Node.val)
         == read($PreCallHeap#3, b##3, _module.Node.val);
    assume b##3 != null
         && b##3 != a#0
         && b##3 != b#0
         && b##3 != c#0
         && b##3 != p#0
         && b##3 != q#0
         && b##3 != r#0
       ==> read($Heap, b##3, _module.Node.tag)
         == read($PreCallHeap#3, b##3, _module.Node.tag);
    assume b##3 != null
         && b##3 != a#0
         && b##3 != b#0
         && b##3 != c#0
         && b##3 != p#0
         && b##3 != q#0
         && b##3 != r#0
       ==> read($Heap, b##3, _module.Node.score)
         == read($PreCallHeap#3, b##3, _module.Node.score);
    assume b##3 != null
         && b##3 != a#0
         && b##3 != b#0
         && b##3 != c#0
         && b##3 != p#0
         && b##3 != q#0
         && b##3 != r#0
       ==> read($Heap, b##3, _module.Node.rank)
         == read($PreCallHeap#3, b##3, _module.Node.rank);
    assume c##3 != null
         && c##3 != a#0
         && c##3 != b#0
         && c##3 != c#0
         && c##3 != p#0
         && c##3 != q#0
         && c##3 != r#0
       ==> read($Heap, c##3, _module.Node.val)
         == read($PreCallHeap#3, c##3, _module.Node.val);
    assume c##3 != null
         && c##3 != a#0
         && c##3 != b#0
         && c##3 != c#0
         && c##3 != p#0
         && c##3 != q#0
         && c##3 != r#0
       ==> read($Heap, c##3, _module.Node.tag)
         == read($PreCallHeap#3, c##3, _module.Node.tag);
    assume c##3 != null
         && c##3 != a#0
         && c##3 != b#0
         && c##3 != c#0
         && c##3 != p#0
         && c##3 != q#0
         && c##3 != r#0
       ==> read($Heap, c##3, _module.Node.score)
         == read($PreCallHeap#3, c##3, _module.Node.score);
    assume c##3 != null
         && c##3 != a#0
         && c##3 != b#0
         && c##3 != c#0
         && c##3 != p#0
         && c##3 != q#0
         && c##3 != r#0
       ==> read($Heap, c##3, _module.Node.rank)
         == read($PreCallHeap#3, c##3, _module.Node.rank);
    assume p##0 != null
         && p##0 != a#0
         && p##0 != b#0
         && p##0 != c#0
         && p##0 != p#0
         && p##0 != q#0
         && p##0 != r#0
       ==> read($Heap, p##0, _module.Node.val)
         == read($PreCallHeap#3, p##0, _module.Node.val);
    assume p##0 != null
         && p##0 != a#0
         && p##0 != b#0
         && p##0 != c#0
         && p##0 != p#0
         && p##0 != q#0
         && p##0 != r#0
       ==> read($Heap, p##0, _module.Node.tag)
         == read($PreCallHeap#3, p##0, _module.Node.tag);
    assume p##0 != null
         && p##0 != a#0
         && p##0 != b#0
         && p##0 != c#0
         && p##0 != p#0
         && p##0 != q#0
         && p##0 != r#0
       ==> read($Heap, p##0, _module.Node.score)
         == read($PreCallHeap#3, p##0, _module.Node.score);
    assume p##0 != null
         && p##0 != a#0
         && p##0 != b#0
         && p##0 != c#0
         && p##0 != p#0
         && p##0 != q#0
         && p##0 != r#0
       ==> read($Heap, p##0, _module.Node.rank)
         == read($PreCallHeap#3, p##0, _module.Node.rank);
    assume q##0 != null
         && q##0 != a#0
         && q##0 != b#0
         && q##0 != c#0
         && q##0 != p#0
         && q##0 != q#0
         && q##0 != r#0
       ==> read($Heap, q##0, _module.Node.val)
         == read($PreCallHeap#3, q##0, _module.Node.val);
    assume q##0 != null
         && q##0 != a#0
         && q##0 != b#0
         && q##0 != c#0
         && q##0 != p#0
         && q##0 != q#0
         && q##0 != r#0
       ==> read($Heap, q##0, _module.Node.tag)
         == read($PreCallHeap#3, q##0, _module.Node.tag);
    assume q##0 != null
         && q##0 != a#0
         && q##0 != b#0
         && q##0 != c#0
         && q##0 != p#0
         && q##0 != q#0
         && q##0 != r#0
       ==> read($Heap, q##0, _module.Node.score)
         == read($PreCallHeap#3, q##0, _module.Node.score);
    assume q##0 != null
         && q##0 != a#0
         && q##0 != b#0
         && q##0 != c#0
         && q##0 != p#0
         && q##0 != q#0
         && q##0 != r#0
       ==> read($Heap, q##0, _module.Node.rank)
         == read($PreCallHeap#3, q##0, _module.Node.rank);
    assume r##0 != null
         && r##0 != a#0
         && r##0 != b#0
         && r##0 != c#0
         && r##0 != p#0
         && r##0 != q#0
         && r##0 != r#0
       ==> read($Heap, r##0, _module.Node.val)
         == read($PreCallHeap#3, r##0, _module.Node.val);
    assume r##0 != null
         && r##0 != a#0
         && r##0 != b#0
         && r##0 != c#0
         && r##0 != p#0
         && r##0 != q#0
         && r##0 != r#0
       ==> read($Heap, r##0, _module.Node.tag)
         == read($PreCallHeap#3, r##0, _module.Node.tag);
    assume r##0 != null
         && r##0 != a#0
         && r##0 != b#0
         && r##0 != c#0
         && r##0 != p#0
         && r##0 != q#0
         && r##0 != r#0
       ==> read($Heap, r##0, _module.Node.score)
         == read($PreCallHeap#3, r##0, _module.Node.score);
    assume r##0 != null
         && r##0 != a#0
         && r##0 != b#0
         && r##0 != c#0
         && r##0 != p#0
         && r##0 != q#0
         && r##0 != r#0
       ==> read($Heap, r##0, _module.Node.rank)
         == read($PreCallHeap#3, r##0, _module.Node.rank);
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
    $PreCallHeap#4 := $Heap;
    $PreCallAlloc#4 := $Alloc;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id2171"} a##4 == a#0
       || a##4 == b#0
       || a##4 == c#0
       || a##4 == d#0
       || a##4 == e#0
       || a##4 == f#0
       || a##4 == p#0
       || a##4 == q#0
       || a##4 == r#0
       || a##4 == s#0
       || a##4 == t#0
       || a##4 == u#0
       || !old($Alloc)[a##4];
    assert {:id "id2172"} b##4 == a#0
       || b##4 == b#0
       || b##4 == c#0
       || b##4 == d#0
       || b##4 == e#0
       || b##4 == f#0
       || b##4 == p#0
       || b##4 == q#0
       || b##4 == r#0
       || b##4 == s#0
       || b##4 == t#0
       || b##4 == u#0
       || !old($Alloc)[b##4];
    assert {:id "id2173"} c##4 == a#0
       || c##4 == b#0
       || c##4 == c#0
       || c##4 == d#0
       || c##4 == e#0
       || c##4 == f#0
       || c##4 == p#0
       || c##4 == q#0
       || c##4 == r#0
       || c##4 == s#0
       || c##4 == t#0
       || c##4 == u#0
       || !old($Alloc)[c##4];
    assert {:id "id2174"} d##3 == a#0
       || d##3 == b#0
       || d##3 == c#0
       || d##3 == d#0
       || d##3 == e#0
       || d##3 == f#0
       || d##3 == p#0
       || d##3 == q#0
       || d##3 == r#0
       || d##3 == s#0
       || d##3 == t#0
       || d##3 == u#0
       || !old($Alloc)[d##3];
    assert {:id "id2175"} e##3 == a#0
       || e##3 == b#0
       || e##3 == c#0
       || e##3 == d#0
       || e##3 == e#0
       || e##3 == f#0
       || e##3 == p#0
       || e##3 == q#0
       || e##3 == r#0
       || e##3 == s#0
       || e##3 == t#0
       || e##3 == u#0
       || !old($Alloc)[e##3];
    assert {:id "id2176"} f##3 == a#0
       || f##3 == b#0
       || f##3 == c#0
       || f##3 == d#0
       || f##3 == e#0
       || f##3 == f#0
       || f##3 == p#0
       || f##3 == q#0
       || f##3 == r#0
       || f##3 == s#0
       || f##3 == t#0
       || f##3 == u#0
       || !old($Alloc)[f##3];
    call {:id "id2177"} Call$$_module.__default.QuadBump(a##4, b##4, c##4, d##3, e##3, f##3);
    // qf-call-frame QuadBump: supports=42 reads=168 modified=6
    assume p#0 != null
         && p#0 != p#0
         && p#0 != q#0
         && p#0 != r#0
         && p#0 != s#0
         && p#0 != t#0
         && p#0 != u#0
       ==> read($Heap, p#0, _module.Node.val)
         == read($PreCallHeap#4, p#0, _module.Node.val);
    assume p#0 != null
         && p#0 != p#0
         && p#0 != q#0
         && p#0 != r#0
         && p#0 != s#0
         && p#0 != t#0
         && p#0 != u#0
       ==> read($Heap, p#0, _module.Node.tag)
         == read($PreCallHeap#4, p#0, _module.Node.tag);
    assume p#0 != null
         && p#0 != p#0
         && p#0 != q#0
         && p#0 != r#0
         && p#0 != s#0
         && p#0 != t#0
         && p#0 != u#0
       ==> read($Heap, p#0, _module.Node.score)
         == read($PreCallHeap#4, p#0, _module.Node.score);
    assume p#0 != null
         && p#0 != p#0
         && p#0 != q#0
         && p#0 != r#0
         && p#0 != s#0
         && p#0 != t#0
         && p#0 != u#0
       ==> read($Heap, p#0, _module.Node.rank)
         == read($PreCallHeap#4, p#0, _module.Node.rank);
    assume q#0 != null
         && q#0 != p#0
         && q#0 != q#0
         && q#0 != r#0
         && q#0 != s#0
         && q#0 != t#0
         && q#0 != u#0
       ==> read($Heap, q#0, _module.Node.val)
         == read($PreCallHeap#4, q#0, _module.Node.val);
    assume q#0 != null
         && q#0 != p#0
         && q#0 != q#0
         && q#0 != r#0
         && q#0 != s#0
         && q#0 != t#0
         && q#0 != u#0
       ==> read($Heap, q#0, _module.Node.tag)
         == read($PreCallHeap#4, q#0, _module.Node.tag);
    assume q#0 != null
         && q#0 != p#0
         && q#0 != q#0
         && q#0 != r#0
         && q#0 != s#0
         && q#0 != t#0
         && q#0 != u#0
       ==> read($Heap, q#0, _module.Node.score)
         == read($PreCallHeap#4, q#0, _module.Node.score);
    assume q#0 != null
         && q#0 != p#0
         && q#0 != q#0
         && q#0 != r#0
         && q#0 != s#0
         && q#0 != t#0
         && q#0 != u#0
       ==> read($Heap, q#0, _module.Node.rank)
         == read($PreCallHeap#4, q#0, _module.Node.rank);
    assume r#0 != null
         && r#0 != p#0
         && r#0 != q#0
         && r#0 != r#0
         && r#0 != s#0
         && r#0 != t#0
         && r#0 != u#0
       ==> read($Heap, r#0, _module.Node.val)
         == read($PreCallHeap#4, r#0, _module.Node.val);
    assume r#0 != null
         && r#0 != p#0
         && r#0 != q#0
         && r#0 != r#0
         && r#0 != s#0
         && r#0 != t#0
         && r#0 != u#0
       ==> read($Heap, r#0, _module.Node.tag)
         == read($PreCallHeap#4, r#0, _module.Node.tag);
    assume r#0 != null
         && r#0 != p#0
         && r#0 != q#0
         && r#0 != r#0
         && r#0 != s#0
         && r#0 != t#0
         && r#0 != u#0
       ==> read($Heap, r#0, _module.Node.score)
         == read($PreCallHeap#4, r#0, _module.Node.score);
    assume r#0 != null
         && r#0 != p#0
         && r#0 != q#0
         && r#0 != r#0
         && r#0 != s#0
         && r#0 != t#0
         && r#0 != u#0
       ==> read($Heap, r#0, _module.Node.rank)
         == read($PreCallHeap#4, r#0, _module.Node.rank);
    assume s#0 != null
         && s#0 != p#0
         && s#0 != q#0
         && s#0 != r#0
         && s#0 != s#0
         && s#0 != t#0
         && s#0 != u#0
       ==> read($Heap, s#0, _module.Node.val)
         == read($PreCallHeap#4, s#0, _module.Node.val);
    assume s#0 != null
         && s#0 != p#0
         && s#0 != q#0
         && s#0 != r#0
         && s#0 != s#0
         && s#0 != t#0
         && s#0 != u#0
       ==> read($Heap, s#0, _module.Node.tag)
         == read($PreCallHeap#4, s#0, _module.Node.tag);
    assume s#0 != null
         && s#0 != p#0
         && s#0 != q#0
         && s#0 != r#0
         && s#0 != s#0
         && s#0 != t#0
         && s#0 != u#0
       ==> read($Heap, s#0, _module.Node.score)
         == read($PreCallHeap#4, s#0, _module.Node.score);
    assume s#0 != null
         && s#0 != p#0
         && s#0 != q#0
         && s#0 != r#0
         && s#0 != s#0
         && s#0 != t#0
         && s#0 != u#0
       ==> read($Heap, s#0, _module.Node.rank)
         == read($PreCallHeap#4, s#0, _module.Node.rank);
    assume t#0 != null
         && t#0 != p#0
         && t#0 != q#0
         && t#0 != r#0
         && t#0 != s#0
         && t#0 != t#0
         && t#0 != u#0
       ==> read($Heap, t#0, _module.Node.val)
         == read($PreCallHeap#4, t#0, _module.Node.val);
    assume t#0 != null
         && t#0 != p#0
         && t#0 != q#0
         && t#0 != r#0
         && t#0 != s#0
         && t#0 != t#0
         && t#0 != u#0
       ==> read($Heap, t#0, _module.Node.tag)
         == read($PreCallHeap#4, t#0, _module.Node.tag);
    assume t#0 != null
         && t#0 != p#0
         && t#0 != q#0
         && t#0 != r#0
         && t#0 != s#0
         && t#0 != t#0
         && t#0 != u#0
       ==> read($Heap, t#0, _module.Node.score)
         == read($PreCallHeap#4, t#0, _module.Node.score);
    assume t#0 != null
         && t#0 != p#0
         && t#0 != q#0
         && t#0 != r#0
         && t#0 != s#0
         && t#0 != t#0
         && t#0 != u#0
       ==> read($Heap, t#0, _module.Node.rank)
         == read($PreCallHeap#4, t#0, _module.Node.rank);
    assume u#0 != null
         && u#0 != p#0
         && u#0 != q#0
         && u#0 != r#0
         && u#0 != s#0
         && u#0 != t#0
         && u#0 != u#0
       ==> read($Heap, u#0, _module.Node.val)
         == read($PreCallHeap#4, u#0, _module.Node.val);
    assume u#0 != null
         && u#0 != p#0
         && u#0 != q#0
         && u#0 != r#0
         && u#0 != s#0
         && u#0 != t#0
         && u#0 != u#0
       ==> read($Heap, u#0, _module.Node.tag)
         == read($PreCallHeap#4, u#0, _module.Node.tag);
    assume u#0 != null
         && u#0 != p#0
         && u#0 != q#0
         && u#0 != r#0
         && u#0 != s#0
         && u#0 != t#0
         && u#0 != u#0
       ==> read($Heap, u#0, _module.Node.score)
         == read($PreCallHeap#4, u#0, _module.Node.score);
    assume u#0 != null
         && u#0 != p#0
         && u#0 != q#0
         && u#0 != r#0
         && u#0 != s#0
         && u#0 != t#0
         && u#0 != u#0
       ==> read($Heap, u#0, _module.Node.rank)
         == read($PreCallHeap#4, u#0, _module.Node.rank);
    assume a#0 != null
         && a#0 != p#0
         && a#0 != q#0
         && a#0 != r#0
         && a#0 != s#0
         && a#0 != t#0
         && a#0 != u#0
       ==> read($Heap, a#0, _module.Node.val)
         == read($PreCallHeap#4, a#0, _module.Node.val);
    assume a#0 != null
         && a#0 != p#0
         && a#0 != q#0
         && a#0 != r#0
         && a#0 != s#0
         && a#0 != t#0
         && a#0 != u#0
       ==> read($Heap, a#0, _module.Node.tag)
         == read($PreCallHeap#4, a#0, _module.Node.tag);
    assume a#0 != null
         && a#0 != p#0
         && a#0 != q#0
         && a#0 != r#0
         && a#0 != s#0
         && a#0 != t#0
         && a#0 != u#0
       ==> read($Heap, a#0, _module.Node.score)
         == read($PreCallHeap#4, a#0, _module.Node.score);
    assume a#0 != null
         && a#0 != p#0
         && a#0 != q#0
         && a#0 != r#0
         && a#0 != s#0
         && a#0 != t#0
         && a#0 != u#0
       ==> read($Heap, a#0, _module.Node.rank)
         == read($PreCallHeap#4, a#0, _module.Node.rank);
    assume b#0 != null
         && b#0 != p#0
         && b#0 != q#0
         && b#0 != r#0
         && b#0 != s#0
         && b#0 != t#0
         && b#0 != u#0
       ==> read($Heap, b#0, _module.Node.val)
         == read($PreCallHeap#4, b#0, _module.Node.val);
    assume b#0 != null
         && b#0 != p#0
         && b#0 != q#0
         && b#0 != r#0
         && b#0 != s#0
         && b#0 != t#0
         && b#0 != u#0
       ==> read($Heap, b#0, _module.Node.tag)
         == read($PreCallHeap#4, b#0, _module.Node.tag);
    assume b#0 != null
         && b#0 != p#0
         && b#0 != q#0
         && b#0 != r#0
         && b#0 != s#0
         && b#0 != t#0
         && b#0 != u#0
       ==> read($Heap, b#0, _module.Node.score)
         == read($PreCallHeap#4, b#0, _module.Node.score);
    assume b#0 != null
         && b#0 != p#0
         && b#0 != q#0
         && b#0 != r#0
         && b#0 != s#0
         && b#0 != t#0
         && b#0 != u#0
       ==> read($Heap, b#0, _module.Node.rank)
         == read($PreCallHeap#4, b#0, _module.Node.rank);
    assume c#0 != null
         && c#0 != p#0
         && c#0 != q#0
         && c#0 != r#0
         && c#0 != s#0
         && c#0 != t#0
         && c#0 != u#0
       ==> read($Heap, c#0, _module.Node.val)
         == read($PreCallHeap#4, c#0, _module.Node.val);
    assume c#0 != null
         && c#0 != p#0
         && c#0 != q#0
         && c#0 != r#0
         && c#0 != s#0
         && c#0 != t#0
         && c#0 != u#0
       ==> read($Heap, c#0, _module.Node.tag)
         == read($PreCallHeap#4, c#0, _module.Node.tag);
    assume c#0 != null
         && c#0 != p#0
         && c#0 != q#0
         && c#0 != r#0
         && c#0 != s#0
         && c#0 != t#0
         && c#0 != u#0
       ==> read($Heap, c#0, _module.Node.score)
         == read($PreCallHeap#4, c#0, _module.Node.score);
    assume c#0 != null
         && c#0 != p#0
         && c#0 != q#0
         && c#0 != r#0
         && c#0 != s#0
         && c#0 != t#0
         && c#0 != u#0
       ==> read($Heap, c#0, _module.Node.rank)
         == read($PreCallHeap#4, c#0, _module.Node.rank);
    assume d#0 != null
         && d#0 != p#0
         && d#0 != q#0
         && d#0 != r#0
         && d#0 != s#0
         && d#0 != t#0
         && d#0 != u#0
       ==> read($Heap, d#0, _module.Node.val)
         == read($PreCallHeap#4, d#0, _module.Node.val);
    assume d#0 != null
         && d#0 != p#0
         && d#0 != q#0
         && d#0 != r#0
         && d#0 != s#0
         && d#0 != t#0
         && d#0 != u#0
       ==> read($Heap, d#0, _module.Node.tag)
         == read($PreCallHeap#4, d#0, _module.Node.tag);
    assume d#0 != null
         && d#0 != p#0
         && d#0 != q#0
         && d#0 != r#0
         && d#0 != s#0
         && d#0 != t#0
         && d#0 != u#0
       ==> read($Heap, d#0, _module.Node.score)
         == read($PreCallHeap#4, d#0, _module.Node.score);
    assume d#0 != null
         && d#0 != p#0
         && d#0 != q#0
         && d#0 != r#0
         && d#0 != s#0
         && d#0 != t#0
         && d#0 != u#0
       ==> read($Heap, d#0, _module.Node.rank)
         == read($PreCallHeap#4, d#0, _module.Node.rank);
    assume e#0 != null
         && e#0 != p#0
         && e#0 != q#0
         && e#0 != r#0
         && e#0 != s#0
         && e#0 != t#0
         && e#0 != u#0
       ==> read($Heap, e#0, _module.Node.val)
         == read($PreCallHeap#4, e#0, _module.Node.val);
    assume e#0 != null
         && e#0 != p#0
         && e#0 != q#0
         && e#0 != r#0
         && e#0 != s#0
         && e#0 != t#0
         && e#0 != u#0
       ==> read($Heap, e#0, _module.Node.tag)
         == read($PreCallHeap#4, e#0, _module.Node.tag);
    assume e#0 != null
         && e#0 != p#0
         && e#0 != q#0
         && e#0 != r#0
         && e#0 != s#0
         && e#0 != t#0
         && e#0 != u#0
       ==> read($Heap, e#0, _module.Node.score)
         == read($PreCallHeap#4, e#0, _module.Node.score);
    assume e#0 != null
         && e#0 != p#0
         && e#0 != q#0
         && e#0 != r#0
         && e#0 != s#0
         && e#0 != t#0
         && e#0 != u#0
       ==> read($Heap, e#0, _module.Node.rank)
         == read($PreCallHeap#4, e#0, _module.Node.rank);
    assume f#0 != null
         && f#0 != p#0
         && f#0 != q#0
         && f#0 != r#0
         && f#0 != s#0
         && f#0 != t#0
         && f#0 != u#0
       ==> read($Heap, f#0, _module.Node.val)
         == read($PreCallHeap#4, f#0, _module.Node.val);
    assume f#0 != null
         && f#0 != p#0
         && f#0 != q#0
         && f#0 != r#0
         && f#0 != s#0
         && f#0 != t#0
         && f#0 != u#0
       ==> read($Heap, f#0, _module.Node.tag)
         == read($PreCallHeap#4, f#0, _module.Node.tag);
    assume f#0 != null
         && f#0 != p#0
         && f#0 != q#0
         && f#0 != r#0
         && f#0 != s#0
         && f#0 != t#0
         && f#0 != u#0
       ==> read($Heap, f#0, _module.Node.score)
         == read($PreCallHeap#4, f#0, _module.Node.score);
    assume f#0 != null
         && f#0 != p#0
         && f#0 != q#0
         && f#0 != r#0
         && f#0 != s#0
         && f#0 != t#0
         && f#0 != u#0
       ==> read($Heap, f#0, _module.Node.rank)
         == read($PreCallHeap#4, f#0, _module.Node.rank);
    assume a##0 != null
         && a##0 != p#0
         && a##0 != q#0
         && a##0 != r#0
         && a##0 != s#0
         && a##0 != t#0
         && a##0 != u#0
       ==> read($Heap, a##0, _module.Node.val)
         == read($PreCallHeap#4, a##0, _module.Node.val);
    assume a##0 != null
         && a##0 != p#0
         && a##0 != q#0
         && a##0 != r#0
         && a##0 != s#0
         && a##0 != t#0
         && a##0 != u#0
       ==> read($Heap, a##0, _module.Node.tag)
         == read($PreCallHeap#4, a##0, _module.Node.tag);
    assume a##0 != null
         && a##0 != p#0
         && a##0 != q#0
         && a##0 != r#0
         && a##0 != s#0
         && a##0 != t#0
         && a##0 != u#0
       ==> read($Heap, a##0, _module.Node.score)
         == read($PreCallHeap#4, a##0, _module.Node.score);
    assume a##0 != null
         && a##0 != p#0
         && a##0 != q#0
         && a##0 != r#0
         && a##0 != s#0
         && a##0 != t#0
         && a##0 != u#0
       ==> read($Heap, a##0, _module.Node.rank)
         == read($PreCallHeap#4, a##0, _module.Node.rank);
    assume b##0 != null
         && b##0 != p#0
         && b##0 != q#0
         && b##0 != r#0
         && b##0 != s#0
         && b##0 != t#0
         && b##0 != u#0
       ==> read($Heap, b##0, _module.Node.val)
         == read($PreCallHeap#4, b##0, _module.Node.val);
    assume b##0 != null
         && b##0 != p#0
         && b##0 != q#0
         && b##0 != r#0
         && b##0 != s#0
         && b##0 != t#0
         && b##0 != u#0
       ==> read($Heap, b##0, _module.Node.tag)
         == read($PreCallHeap#4, b##0, _module.Node.tag);
    assume b##0 != null
         && b##0 != p#0
         && b##0 != q#0
         && b##0 != r#0
         && b##0 != s#0
         && b##0 != t#0
         && b##0 != u#0
       ==> read($Heap, b##0, _module.Node.score)
         == read($PreCallHeap#4, b##0, _module.Node.score);
    assume b##0 != null
         && b##0 != p#0
         && b##0 != q#0
         && b##0 != r#0
         && b##0 != s#0
         && b##0 != t#0
         && b##0 != u#0
       ==> read($Heap, b##0, _module.Node.rank)
         == read($PreCallHeap#4, b##0, _module.Node.rank);
    assume c##0 != null
         && c##0 != p#0
         && c##0 != q#0
         && c##0 != r#0
         && c##0 != s#0
         && c##0 != t#0
         && c##0 != u#0
       ==> read($Heap, c##0, _module.Node.val)
         == read($PreCallHeap#4, c##0, _module.Node.val);
    assume c##0 != null
         && c##0 != p#0
         && c##0 != q#0
         && c##0 != r#0
         && c##0 != s#0
         && c##0 != t#0
         && c##0 != u#0
       ==> read($Heap, c##0, _module.Node.tag)
         == read($PreCallHeap#4, c##0, _module.Node.tag);
    assume c##0 != null
         && c##0 != p#0
         && c##0 != q#0
         && c##0 != r#0
         && c##0 != s#0
         && c##0 != t#0
         && c##0 != u#0
       ==> read($Heap, c##0, _module.Node.score)
         == read($PreCallHeap#4, c##0, _module.Node.score);
    assume c##0 != null
         && c##0 != p#0
         && c##0 != q#0
         && c##0 != r#0
         && c##0 != s#0
         && c##0 != t#0
         && c##0 != u#0
       ==> read($Heap, c##0, _module.Node.rank)
         == read($PreCallHeap#4, c##0, _module.Node.rank);
    assume d##0 != null
         && d##0 != p#0
         && d##0 != q#0
         && d##0 != r#0
         && d##0 != s#0
         && d##0 != t#0
         && d##0 != u#0
       ==> read($Heap, d##0, _module.Node.val)
         == read($PreCallHeap#4, d##0, _module.Node.val);
    assume d##0 != null
         && d##0 != p#0
         && d##0 != q#0
         && d##0 != r#0
         && d##0 != s#0
         && d##0 != t#0
         && d##0 != u#0
       ==> read($Heap, d##0, _module.Node.tag)
         == read($PreCallHeap#4, d##0, _module.Node.tag);
    assume d##0 != null
         && d##0 != p#0
         && d##0 != q#0
         && d##0 != r#0
         && d##0 != s#0
         && d##0 != t#0
         && d##0 != u#0
       ==> read($Heap, d##0, _module.Node.score)
         == read($PreCallHeap#4, d##0, _module.Node.score);
    assume d##0 != null
         && d##0 != p#0
         && d##0 != q#0
         && d##0 != r#0
         && d##0 != s#0
         && d##0 != t#0
         && d##0 != u#0
       ==> read($Heap, d##0, _module.Node.rank)
         == read($PreCallHeap#4, d##0, _module.Node.rank);
    assume e##0 != null
         && e##0 != p#0
         && e##0 != q#0
         && e##0 != r#0
         && e##0 != s#0
         && e##0 != t#0
         && e##0 != u#0
       ==> read($Heap, e##0, _module.Node.val)
         == read($PreCallHeap#4, e##0, _module.Node.val);
    assume e##0 != null
         && e##0 != p#0
         && e##0 != q#0
         && e##0 != r#0
         && e##0 != s#0
         && e##0 != t#0
         && e##0 != u#0
       ==> read($Heap, e##0, _module.Node.tag)
         == read($PreCallHeap#4, e##0, _module.Node.tag);
    assume e##0 != null
         && e##0 != p#0
         && e##0 != q#0
         && e##0 != r#0
         && e##0 != s#0
         && e##0 != t#0
         && e##0 != u#0
       ==> read($Heap, e##0, _module.Node.score)
         == read($PreCallHeap#4, e##0, _module.Node.score);
    assume e##0 != null
         && e##0 != p#0
         && e##0 != q#0
         && e##0 != r#0
         && e##0 != s#0
         && e##0 != t#0
         && e##0 != u#0
       ==> read($Heap, e##0, _module.Node.rank)
         == read($PreCallHeap#4, e##0, _module.Node.rank);
    assume f##0 != null
         && f##0 != p#0
         && f##0 != q#0
         && f##0 != r#0
         && f##0 != s#0
         && f##0 != t#0
         && f##0 != u#0
       ==> read($Heap, f##0, _module.Node.val)
         == read($PreCallHeap#4, f##0, _module.Node.val);
    assume f##0 != null
         && f##0 != p#0
         && f##0 != q#0
         && f##0 != r#0
         && f##0 != s#0
         && f##0 != t#0
         && f##0 != u#0
       ==> read($Heap, f##0, _module.Node.tag)
         == read($PreCallHeap#4, f##0, _module.Node.tag);
    assume f##0 != null
         && f##0 != p#0
         && f##0 != q#0
         && f##0 != r#0
         && f##0 != s#0
         && f##0 != t#0
         && f##0 != u#0
       ==> read($Heap, f##0, _module.Node.score)
         == read($PreCallHeap#4, f##0, _module.Node.score);
    assume f##0 != null
         && f##0 != p#0
         && f##0 != q#0
         && f##0 != r#0
         && f##0 != s#0
         && f##0 != t#0
         && f##0 != u#0
       ==> read($Heap, f##0, _module.Node.rank)
         == read($PreCallHeap#4, f##0, _module.Node.rank);
    assume a##1 != null
         && a##1 != p#0
         && a##1 != q#0
         && a##1 != r#0
         && a##1 != s#0
         && a##1 != t#0
         && a##1 != u#0
       ==> read($Heap, a##1, _module.Node.val)
         == read($PreCallHeap#4, a##1, _module.Node.val);
    assume a##1 != null
         && a##1 != p#0
         && a##1 != q#0
         && a##1 != r#0
         && a##1 != s#0
         && a##1 != t#0
         && a##1 != u#0
       ==> read($Heap, a##1, _module.Node.tag)
         == read($PreCallHeap#4, a##1, _module.Node.tag);
    assume a##1 != null
         && a##1 != p#0
         && a##1 != q#0
         && a##1 != r#0
         && a##1 != s#0
         && a##1 != t#0
         && a##1 != u#0
       ==> read($Heap, a##1, _module.Node.score)
         == read($PreCallHeap#4, a##1, _module.Node.score);
    assume a##1 != null
         && a##1 != p#0
         && a##1 != q#0
         && a##1 != r#0
         && a##1 != s#0
         && a##1 != t#0
         && a##1 != u#0
       ==> read($Heap, a##1, _module.Node.rank)
         == read($PreCallHeap#4, a##1, _module.Node.rank);
    assume b##1 != null
         && b##1 != p#0
         && b##1 != q#0
         && b##1 != r#0
         && b##1 != s#0
         && b##1 != t#0
         && b##1 != u#0
       ==> read($Heap, b##1, _module.Node.val)
         == read($PreCallHeap#4, b##1, _module.Node.val);
    assume b##1 != null
         && b##1 != p#0
         && b##1 != q#0
         && b##1 != r#0
         && b##1 != s#0
         && b##1 != t#0
         && b##1 != u#0
       ==> read($Heap, b##1, _module.Node.tag)
         == read($PreCallHeap#4, b##1, _module.Node.tag);
    assume b##1 != null
         && b##1 != p#0
         && b##1 != q#0
         && b##1 != r#0
         && b##1 != s#0
         && b##1 != t#0
         && b##1 != u#0
       ==> read($Heap, b##1, _module.Node.score)
         == read($PreCallHeap#4, b##1, _module.Node.score);
    assume b##1 != null
         && b##1 != p#0
         && b##1 != q#0
         && b##1 != r#0
         && b##1 != s#0
         && b##1 != t#0
         && b##1 != u#0
       ==> read($Heap, b##1, _module.Node.rank)
         == read($PreCallHeap#4, b##1, _module.Node.rank);
    assume c##1 != null
         && c##1 != p#0
         && c##1 != q#0
         && c##1 != r#0
         && c##1 != s#0
         && c##1 != t#0
         && c##1 != u#0
       ==> read($Heap, c##1, _module.Node.val)
         == read($PreCallHeap#4, c##1, _module.Node.val);
    assume c##1 != null
         && c##1 != p#0
         && c##1 != q#0
         && c##1 != r#0
         && c##1 != s#0
         && c##1 != t#0
         && c##1 != u#0
       ==> read($Heap, c##1, _module.Node.tag)
         == read($PreCallHeap#4, c##1, _module.Node.tag);
    assume c##1 != null
         && c##1 != p#0
         && c##1 != q#0
         && c##1 != r#0
         && c##1 != s#0
         && c##1 != t#0
         && c##1 != u#0
       ==> read($Heap, c##1, _module.Node.score)
         == read($PreCallHeap#4, c##1, _module.Node.score);
    assume c##1 != null
         && c##1 != p#0
         && c##1 != q#0
         && c##1 != r#0
         && c##1 != s#0
         && c##1 != t#0
         && c##1 != u#0
       ==> read($Heap, c##1, _module.Node.rank)
         == read($PreCallHeap#4, c##1, _module.Node.rank);
    assume d##1 != null
         && d##1 != p#0
         && d##1 != q#0
         && d##1 != r#0
         && d##1 != s#0
         && d##1 != t#0
         && d##1 != u#0
       ==> read($Heap, d##1, _module.Node.val)
         == read($PreCallHeap#4, d##1, _module.Node.val);
    assume d##1 != null
         && d##1 != p#0
         && d##1 != q#0
         && d##1 != r#0
         && d##1 != s#0
         && d##1 != t#0
         && d##1 != u#0
       ==> read($Heap, d##1, _module.Node.tag)
         == read($PreCallHeap#4, d##1, _module.Node.tag);
    assume d##1 != null
         && d##1 != p#0
         && d##1 != q#0
         && d##1 != r#0
         && d##1 != s#0
         && d##1 != t#0
         && d##1 != u#0
       ==> read($Heap, d##1, _module.Node.score)
         == read($PreCallHeap#4, d##1, _module.Node.score);
    assume d##1 != null
         && d##1 != p#0
         && d##1 != q#0
         && d##1 != r#0
         && d##1 != s#0
         && d##1 != t#0
         && d##1 != u#0
       ==> read($Heap, d##1, _module.Node.rank)
         == read($PreCallHeap#4, d##1, _module.Node.rank);
    assume e##1 != null
         && e##1 != p#0
         && e##1 != q#0
         && e##1 != r#0
         && e##1 != s#0
         && e##1 != t#0
         && e##1 != u#0
       ==> read($Heap, e##1, _module.Node.val)
         == read($PreCallHeap#4, e##1, _module.Node.val);
    assume e##1 != null
         && e##1 != p#0
         && e##1 != q#0
         && e##1 != r#0
         && e##1 != s#0
         && e##1 != t#0
         && e##1 != u#0
       ==> read($Heap, e##1, _module.Node.tag)
         == read($PreCallHeap#4, e##1, _module.Node.tag);
    assume e##1 != null
         && e##1 != p#0
         && e##1 != q#0
         && e##1 != r#0
         && e##1 != s#0
         && e##1 != t#0
         && e##1 != u#0
       ==> read($Heap, e##1, _module.Node.score)
         == read($PreCallHeap#4, e##1, _module.Node.score);
    assume e##1 != null
         && e##1 != p#0
         && e##1 != q#0
         && e##1 != r#0
         && e##1 != s#0
         && e##1 != t#0
         && e##1 != u#0
       ==> read($Heap, e##1, _module.Node.rank)
         == read($PreCallHeap#4, e##1, _module.Node.rank);
    assume f##1 != null
         && f##1 != p#0
         && f##1 != q#0
         && f##1 != r#0
         && f##1 != s#0
         && f##1 != t#0
         && f##1 != u#0
       ==> read($Heap, f##1, _module.Node.val)
         == read($PreCallHeap#4, f##1, _module.Node.val);
    assume f##1 != null
         && f##1 != p#0
         && f##1 != q#0
         && f##1 != r#0
         && f##1 != s#0
         && f##1 != t#0
         && f##1 != u#0
       ==> read($Heap, f##1, _module.Node.tag)
         == read($PreCallHeap#4, f##1, _module.Node.tag);
    assume f##1 != null
         && f##1 != p#0
         && f##1 != q#0
         && f##1 != r#0
         && f##1 != s#0
         && f##1 != t#0
         && f##1 != u#0
       ==> read($Heap, f##1, _module.Node.score)
         == read($PreCallHeap#4, f##1, _module.Node.score);
    assume f##1 != null
         && f##1 != p#0
         && f##1 != q#0
         && f##1 != r#0
         && f##1 != s#0
         && f##1 != t#0
         && f##1 != u#0
       ==> read($Heap, f##1, _module.Node.rank)
         == read($PreCallHeap#4, f##1, _module.Node.rank);
    assume a##2 != null
         && a##2 != p#0
         && a##2 != q#0
         && a##2 != r#0
         && a##2 != s#0
         && a##2 != t#0
         && a##2 != u#0
       ==> read($Heap, a##2, _module.Node.val)
         == read($PreCallHeap#4, a##2, _module.Node.val);
    assume a##2 != null
         && a##2 != p#0
         && a##2 != q#0
         && a##2 != r#0
         && a##2 != s#0
         && a##2 != t#0
         && a##2 != u#0
       ==> read($Heap, a##2, _module.Node.tag)
         == read($PreCallHeap#4, a##2, _module.Node.tag);
    assume a##2 != null
         && a##2 != p#0
         && a##2 != q#0
         && a##2 != r#0
         && a##2 != s#0
         && a##2 != t#0
         && a##2 != u#0
       ==> read($Heap, a##2, _module.Node.score)
         == read($PreCallHeap#4, a##2, _module.Node.score);
    assume a##2 != null
         && a##2 != p#0
         && a##2 != q#0
         && a##2 != r#0
         && a##2 != s#0
         && a##2 != t#0
         && a##2 != u#0
       ==> read($Heap, a##2, _module.Node.rank)
         == read($PreCallHeap#4, a##2, _module.Node.rank);
    assume b##2 != null
         && b##2 != p#0
         && b##2 != q#0
         && b##2 != r#0
         && b##2 != s#0
         && b##2 != t#0
         && b##2 != u#0
       ==> read($Heap, b##2, _module.Node.val)
         == read($PreCallHeap#4, b##2, _module.Node.val);
    assume b##2 != null
         && b##2 != p#0
         && b##2 != q#0
         && b##2 != r#0
         && b##2 != s#0
         && b##2 != t#0
         && b##2 != u#0
       ==> read($Heap, b##2, _module.Node.tag)
         == read($PreCallHeap#4, b##2, _module.Node.tag);
    assume b##2 != null
         && b##2 != p#0
         && b##2 != q#0
         && b##2 != r#0
         && b##2 != s#0
         && b##2 != t#0
         && b##2 != u#0
       ==> read($Heap, b##2, _module.Node.score)
         == read($PreCallHeap#4, b##2, _module.Node.score);
    assume b##2 != null
         && b##2 != p#0
         && b##2 != q#0
         && b##2 != r#0
         && b##2 != s#0
         && b##2 != t#0
         && b##2 != u#0
       ==> read($Heap, b##2, _module.Node.rank)
         == read($PreCallHeap#4, b##2, _module.Node.rank);
    assume c##2 != null
         && c##2 != p#0
         && c##2 != q#0
         && c##2 != r#0
         && c##2 != s#0
         && c##2 != t#0
         && c##2 != u#0
       ==> read($Heap, c##2, _module.Node.val)
         == read($PreCallHeap#4, c##2, _module.Node.val);
    assume c##2 != null
         && c##2 != p#0
         && c##2 != q#0
         && c##2 != r#0
         && c##2 != s#0
         && c##2 != t#0
         && c##2 != u#0
       ==> read($Heap, c##2, _module.Node.tag)
         == read($PreCallHeap#4, c##2, _module.Node.tag);
    assume c##2 != null
         && c##2 != p#0
         && c##2 != q#0
         && c##2 != r#0
         && c##2 != s#0
         && c##2 != t#0
         && c##2 != u#0
       ==> read($Heap, c##2, _module.Node.score)
         == read($PreCallHeap#4, c##2, _module.Node.score);
    assume c##2 != null
         && c##2 != p#0
         && c##2 != q#0
         && c##2 != r#0
         && c##2 != s#0
         && c##2 != t#0
         && c##2 != u#0
       ==> read($Heap, c##2, _module.Node.rank)
         == read($PreCallHeap#4, c##2, _module.Node.rank);
    assume d##2 != null
         && d##2 != p#0
         && d##2 != q#0
         && d##2 != r#0
         && d##2 != s#0
         && d##2 != t#0
         && d##2 != u#0
       ==> read($Heap, d##2, _module.Node.val)
         == read($PreCallHeap#4, d##2, _module.Node.val);
    assume d##2 != null
         && d##2 != p#0
         && d##2 != q#0
         && d##2 != r#0
         && d##2 != s#0
         && d##2 != t#0
         && d##2 != u#0
       ==> read($Heap, d##2, _module.Node.tag)
         == read($PreCallHeap#4, d##2, _module.Node.tag);
    assume d##2 != null
         && d##2 != p#0
         && d##2 != q#0
         && d##2 != r#0
         && d##2 != s#0
         && d##2 != t#0
         && d##2 != u#0
       ==> read($Heap, d##2, _module.Node.score)
         == read($PreCallHeap#4, d##2, _module.Node.score);
    assume d##2 != null
         && d##2 != p#0
         && d##2 != q#0
         && d##2 != r#0
         && d##2 != s#0
         && d##2 != t#0
         && d##2 != u#0
       ==> read($Heap, d##2, _module.Node.rank)
         == read($PreCallHeap#4, d##2, _module.Node.rank);
    assume e##2 != null
         && e##2 != p#0
         && e##2 != q#0
         && e##2 != r#0
         && e##2 != s#0
         && e##2 != t#0
         && e##2 != u#0
       ==> read($Heap, e##2, _module.Node.val)
         == read($PreCallHeap#4, e##2, _module.Node.val);
    assume e##2 != null
         && e##2 != p#0
         && e##2 != q#0
         && e##2 != r#0
         && e##2 != s#0
         && e##2 != t#0
         && e##2 != u#0
       ==> read($Heap, e##2, _module.Node.tag)
         == read($PreCallHeap#4, e##2, _module.Node.tag);
    assume e##2 != null
         && e##2 != p#0
         && e##2 != q#0
         && e##2 != r#0
         && e##2 != s#0
         && e##2 != t#0
         && e##2 != u#0
       ==> read($Heap, e##2, _module.Node.score)
         == read($PreCallHeap#4, e##2, _module.Node.score);
    assume e##2 != null
         && e##2 != p#0
         && e##2 != q#0
         && e##2 != r#0
         && e##2 != s#0
         && e##2 != t#0
         && e##2 != u#0
       ==> read($Heap, e##2, _module.Node.rank)
         == read($PreCallHeap#4, e##2, _module.Node.rank);
    assume f##2 != null
         && f##2 != p#0
         && f##2 != q#0
         && f##2 != r#0
         && f##2 != s#0
         && f##2 != t#0
         && f##2 != u#0
       ==> read($Heap, f##2, _module.Node.val)
         == read($PreCallHeap#4, f##2, _module.Node.val);
    assume f##2 != null
         && f##2 != p#0
         && f##2 != q#0
         && f##2 != r#0
         && f##2 != s#0
         && f##2 != t#0
         && f##2 != u#0
       ==> read($Heap, f##2, _module.Node.tag)
         == read($PreCallHeap#4, f##2, _module.Node.tag);
    assume f##2 != null
         && f##2 != p#0
         && f##2 != q#0
         && f##2 != r#0
         && f##2 != s#0
         && f##2 != t#0
         && f##2 != u#0
       ==> read($Heap, f##2, _module.Node.score)
         == read($PreCallHeap#4, f##2, _module.Node.score);
    assume f##2 != null
         && f##2 != p#0
         && f##2 != q#0
         && f##2 != r#0
         && f##2 != s#0
         && f##2 != t#0
         && f##2 != u#0
       ==> read($Heap, f##2, _module.Node.rank)
         == read($PreCallHeap#4, f##2, _module.Node.rank);
    assume a##3 != null
         && a##3 != p#0
         && a##3 != q#0
         && a##3 != r#0
         && a##3 != s#0
         && a##3 != t#0
         && a##3 != u#0
       ==> read($Heap, a##3, _module.Node.val)
         == read($PreCallHeap#4, a##3, _module.Node.val);
    assume a##3 != null
         && a##3 != p#0
         && a##3 != q#0
         && a##3 != r#0
         && a##3 != s#0
         && a##3 != t#0
         && a##3 != u#0
       ==> read($Heap, a##3, _module.Node.tag)
         == read($PreCallHeap#4, a##3, _module.Node.tag);
    assume a##3 != null
         && a##3 != p#0
         && a##3 != q#0
         && a##3 != r#0
         && a##3 != s#0
         && a##3 != t#0
         && a##3 != u#0
       ==> read($Heap, a##3, _module.Node.score)
         == read($PreCallHeap#4, a##3, _module.Node.score);
    assume a##3 != null
         && a##3 != p#0
         && a##3 != q#0
         && a##3 != r#0
         && a##3 != s#0
         && a##3 != t#0
         && a##3 != u#0
       ==> read($Heap, a##3, _module.Node.rank)
         == read($PreCallHeap#4, a##3, _module.Node.rank);
    assume b##3 != null
         && b##3 != p#0
         && b##3 != q#0
         && b##3 != r#0
         && b##3 != s#0
         && b##3 != t#0
         && b##3 != u#0
       ==> read($Heap, b##3, _module.Node.val)
         == read($PreCallHeap#4, b##3, _module.Node.val);
    assume b##3 != null
         && b##3 != p#0
         && b##3 != q#0
         && b##3 != r#0
         && b##3 != s#0
         && b##3 != t#0
         && b##3 != u#0
       ==> read($Heap, b##3, _module.Node.tag)
         == read($PreCallHeap#4, b##3, _module.Node.tag);
    assume b##3 != null
         && b##3 != p#0
         && b##3 != q#0
         && b##3 != r#0
         && b##3 != s#0
         && b##3 != t#0
         && b##3 != u#0
       ==> read($Heap, b##3, _module.Node.score)
         == read($PreCallHeap#4, b##3, _module.Node.score);
    assume b##3 != null
         && b##3 != p#0
         && b##3 != q#0
         && b##3 != r#0
         && b##3 != s#0
         && b##3 != t#0
         && b##3 != u#0
       ==> read($Heap, b##3, _module.Node.rank)
         == read($PreCallHeap#4, b##3, _module.Node.rank);
    assume c##3 != null
         && c##3 != p#0
         && c##3 != q#0
         && c##3 != r#0
         && c##3 != s#0
         && c##3 != t#0
         && c##3 != u#0
       ==> read($Heap, c##3, _module.Node.val)
         == read($PreCallHeap#4, c##3, _module.Node.val);
    assume c##3 != null
         && c##3 != p#0
         && c##3 != q#0
         && c##3 != r#0
         && c##3 != s#0
         && c##3 != t#0
         && c##3 != u#0
       ==> read($Heap, c##3, _module.Node.tag)
         == read($PreCallHeap#4, c##3, _module.Node.tag);
    assume c##3 != null
         && c##3 != p#0
         && c##3 != q#0
         && c##3 != r#0
         && c##3 != s#0
         && c##3 != t#0
         && c##3 != u#0
       ==> read($Heap, c##3, _module.Node.score)
         == read($PreCallHeap#4, c##3, _module.Node.score);
    assume c##3 != null
         && c##3 != p#0
         && c##3 != q#0
         && c##3 != r#0
         && c##3 != s#0
         && c##3 != t#0
         && c##3 != u#0
       ==> read($Heap, c##3, _module.Node.rank)
         == read($PreCallHeap#4, c##3, _module.Node.rank);
    assume p##0 != null
         && p##0 != p#0
         && p##0 != q#0
         && p##0 != r#0
         && p##0 != s#0
         && p##0 != t#0
         && p##0 != u#0
       ==> read($Heap, p##0, _module.Node.val)
         == read($PreCallHeap#4, p##0, _module.Node.val);
    assume p##0 != null
         && p##0 != p#0
         && p##0 != q#0
         && p##0 != r#0
         && p##0 != s#0
         && p##0 != t#0
         && p##0 != u#0
       ==> read($Heap, p##0, _module.Node.tag)
         == read($PreCallHeap#4, p##0, _module.Node.tag);
    assume p##0 != null
         && p##0 != p#0
         && p##0 != q#0
         && p##0 != r#0
         && p##0 != s#0
         && p##0 != t#0
         && p##0 != u#0
       ==> read($Heap, p##0, _module.Node.score)
         == read($PreCallHeap#4, p##0, _module.Node.score);
    assume p##0 != null
         && p##0 != p#0
         && p##0 != q#0
         && p##0 != r#0
         && p##0 != s#0
         && p##0 != t#0
         && p##0 != u#0
       ==> read($Heap, p##0, _module.Node.rank)
         == read($PreCallHeap#4, p##0, _module.Node.rank);
    assume q##0 != null
         && q##0 != p#0
         && q##0 != q#0
         && q##0 != r#0
         && q##0 != s#0
         && q##0 != t#0
         && q##0 != u#0
       ==> read($Heap, q##0, _module.Node.val)
         == read($PreCallHeap#4, q##0, _module.Node.val);
    assume q##0 != null
         && q##0 != p#0
         && q##0 != q#0
         && q##0 != r#0
         && q##0 != s#0
         && q##0 != t#0
         && q##0 != u#0
       ==> read($Heap, q##0, _module.Node.tag)
         == read($PreCallHeap#4, q##0, _module.Node.tag);
    assume q##0 != null
         && q##0 != p#0
         && q##0 != q#0
         && q##0 != r#0
         && q##0 != s#0
         && q##0 != t#0
         && q##0 != u#0
       ==> read($Heap, q##0, _module.Node.score)
         == read($PreCallHeap#4, q##0, _module.Node.score);
    assume q##0 != null
         && q##0 != p#0
         && q##0 != q#0
         && q##0 != r#0
         && q##0 != s#0
         && q##0 != t#0
         && q##0 != u#0
       ==> read($Heap, q##0, _module.Node.rank)
         == read($PreCallHeap#4, q##0, _module.Node.rank);
    assume r##0 != null
         && r##0 != p#0
         && r##0 != q#0
         && r##0 != r#0
         && r##0 != s#0
         && r##0 != t#0
         && r##0 != u#0
       ==> read($Heap, r##0, _module.Node.val)
         == read($PreCallHeap#4, r##0, _module.Node.val);
    assume r##0 != null
         && r##0 != p#0
         && r##0 != q#0
         && r##0 != r#0
         && r##0 != s#0
         && r##0 != t#0
         && r##0 != u#0
       ==> read($Heap, r##0, _module.Node.tag)
         == read($PreCallHeap#4, r##0, _module.Node.tag);
    assume r##0 != null
         && r##0 != p#0
         && r##0 != q#0
         && r##0 != r#0
         && r##0 != s#0
         && r##0 != t#0
         && r##0 != u#0
       ==> read($Heap, r##0, _module.Node.score)
         == read($PreCallHeap#4, r##0, _module.Node.score);
    assume r##0 != null
         && r##0 != p#0
         && r##0 != q#0
         && r##0 != r#0
         && r##0 != s#0
         && r##0 != t#0
         && r##0 != u#0
       ==> read($Heap, r##0, _module.Node.rank)
         == read($PreCallHeap#4, r##0, _module.Node.rank);
    assume a##4 != null
         && a##4 != p#0
         && a##4 != q#0
         && a##4 != r#0
         && a##4 != s#0
         && a##4 != t#0
         && a##4 != u#0
       ==> read($Heap, a##4, _module.Node.val)
         == read($PreCallHeap#4, a##4, _module.Node.val);
    assume a##4 != null
         && a##4 != p#0
         && a##4 != q#0
         && a##4 != r#0
         && a##4 != s#0
         && a##4 != t#0
         && a##4 != u#0
       ==> read($Heap, a##4, _module.Node.tag)
         == read($PreCallHeap#4, a##4, _module.Node.tag);
    assume a##4 != null
         && a##4 != p#0
         && a##4 != q#0
         && a##4 != r#0
         && a##4 != s#0
         && a##4 != t#0
         && a##4 != u#0
       ==> read($Heap, a##4, _module.Node.score)
         == read($PreCallHeap#4, a##4, _module.Node.score);
    assume a##4 != null
         && a##4 != p#0
         && a##4 != q#0
         && a##4 != r#0
         && a##4 != s#0
         && a##4 != t#0
         && a##4 != u#0
       ==> read($Heap, a##4, _module.Node.rank)
         == read($PreCallHeap#4, a##4, _module.Node.rank);
    assume b##4 != null
         && b##4 != p#0
         && b##4 != q#0
         && b##4 != r#0
         && b##4 != s#0
         && b##4 != t#0
         && b##4 != u#0
       ==> read($Heap, b##4, _module.Node.val)
         == read($PreCallHeap#4, b##4, _module.Node.val);
    assume b##4 != null
         && b##4 != p#0
         && b##4 != q#0
         && b##4 != r#0
         && b##4 != s#0
         && b##4 != t#0
         && b##4 != u#0
       ==> read($Heap, b##4, _module.Node.tag)
         == read($PreCallHeap#4, b##4, _module.Node.tag);
    assume b##4 != null
         && b##4 != p#0
         && b##4 != q#0
         && b##4 != r#0
         && b##4 != s#0
         && b##4 != t#0
         && b##4 != u#0
       ==> read($Heap, b##4, _module.Node.score)
         == read($PreCallHeap#4, b##4, _module.Node.score);
    assume b##4 != null
         && b##4 != p#0
         && b##4 != q#0
         && b##4 != r#0
         && b##4 != s#0
         && b##4 != t#0
         && b##4 != u#0
       ==> read($Heap, b##4, _module.Node.rank)
         == read($PreCallHeap#4, b##4, _module.Node.rank);
    assume c##4 != null
         && c##4 != p#0
         && c##4 != q#0
         && c##4 != r#0
         && c##4 != s#0
         && c##4 != t#0
         && c##4 != u#0
       ==> read($Heap, c##4, _module.Node.val)
         == read($PreCallHeap#4, c##4, _module.Node.val);
    assume c##4 != null
         && c##4 != p#0
         && c##4 != q#0
         && c##4 != r#0
         && c##4 != s#0
         && c##4 != t#0
         && c##4 != u#0
       ==> read($Heap, c##4, _module.Node.tag)
         == read($PreCallHeap#4, c##4, _module.Node.tag);
    assume c##4 != null
         && c##4 != p#0
         && c##4 != q#0
         && c##4 != r#0
         && c##4 != s#0
         && c##4 != t#0
         && c##4 != u#0
       ==> read($Heap, c##4, _module.Node.score)
         == read($PreCallHeap#4, c##4, _module.Node.score);
    assume c##4 != null
         && c##4 != p#0
         && c##4 != q#0
         && c##4 != r#0
         && c##4 != s#0
         && c##4 != t#0
         && c##4 != u#0
       ==> read($Heap, c##4, _module.Node.rank)
         == read($PreCallHeap#4, c##4, _module.Node.rank);
    assume d##3 != null
         && d##3 != p#0
         && d##3 != q#0
         && d##3 != r#0
         && d##3 != s#0
         && d##3 != t#0
         && d##3 != u#0
       ==> read($Heap, d##3, _module.Node.val)
         == read($PreCallHeap#4, d##3, _module.Node.val);
    assume d##3 != null
         && d##3 != p#0
         && d##3 != q#0
         && d##3 != r#0
         && d##3 != s#0
         && d##3 != t#0
         && d##3 != u#0
       ==> read($Heap, d##3, _module.Node.tag)
         == read($PreCallHeap#4, d##3, _module.Node.tag);
    assume d##3 != null
         && d##3 != p#0
         && d##3 != q#0
         && d##3 != r#0
         && d##3 != s#0
         && d##3 != t#0
         && d##3 != u#0
       ==> read($Heap, d##3, _module.Node.score)
         == read($PreCallHeap#4, d##3, _module.Node.score);
    assume d##3 != null
         && d##3 != p#0
         && d##3 != q#0
         && d##3 != r#0
         && d##3 != s#0
         && d##3 != t#0
         && d##3 != u#0
       ==> read($Heap, d##3, _module.Node.rank)
         == read($PreCallHeap#4, d##3, _module.Node.rank);
    assume e##3 != null
         && e##3 != p#0
         && e##3 != q#0
         && e##3 != r#0
         && e##3 != s#0
         && e##3 != t#0
         && e##3 != u#0
       ==> read($Heap, e##3, _module.Node.val)
         == read($PreCallHeap#4, e##3, _module.Node.val);
    assume e##3 != null
         && e##3 != p#0
         && e##3 != q#0
         && e##3 != r#0
         && e##3 != s#0
         && e##3 != t#0
         && e##3 != u#0
       ==> read($Heap, e##3, _module.Node.tag)
         == read($PreCallHeap#4, e##3, _module.Node.tag);
    assume e##3 != null
         && e##3 != p#0
         && e##3 != q#0
         && e##3 != r#0
         && e##3 != s#0
         && e##3 != t#0
         && e##3 != u#0
       ==> read($Heap, e##3, _module.Node.score)
         == read($PreCallHeap#4, e##3, _module.Node.score);
    assume e##3 != null
         && e##3 != p#0
         && e##3 != q#0
         && e##3 != r#0
         && e##3 != s#0
         && e##3 != t#0
         && e##3 != u#0
       ==> read($Heap, e##3, _module.Node.rank)
         == read($PreCallHeap#4, e##3, _module.Node.rank);
    assume f##3 != null
         && f##3 != p#0
         && f##3 != q#0
         && f##3 != r#0
         && f##3 != s#0
         && f##3 != t#0
         && f##3 != u#0
       ==> read($Heap, f##3, _module.Node.val)
         == read($PreCallHeap#4, f##3, _module.Node.val);
    assume f##3 != null
         && f##3 != p#0
         && f##3 != q#0
         && f##3 != r#0
         && f##3 != s#0
         && f##3 != t#0
         && f##3 != u#0
       ==> read($Heap, f##3, _module.Node.tag)
         == read($PreCallHeap#4, f##3, _module.Node.tag);
    assume f##3 != null
         && f##3 != p#0
         && f##3 != q#0
         && f##3 != r#0
         && f##3 != s#0
         && f##3 != t#0
         && f##3 != u#0
       ==> read($Heap, f##3, _module.Node.score)
         == read($PreCallHeap#4, f##3, _module.Node.score);
    assume f##3 != null
         && f##3 != p#0
         && f##3 != q#0
         && f##3 != r#0
         && f##3 != s#0
         && f##3 != t#0
         && f##3 != u#0
       ==> read($Heap, f##3, _module.Node.rank)
         == read($PreCallHeap#4, f##3, _module.Node.rank);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(234,28)"} true;
}



const unique class._module.Node?: ClassName;

const _module.Node.val: Field
uses {
axiom FDim(_module.Node.val) == 0
   && FieldOfDecl(class._module.Node?, field$val) == _module.Node.val
   && !$IsGhostField(_module.Node.val);
}

const _module.Node.tag: Field
uses {
axiom FDim(_module.Node.tag) == 0
   && FieldOfDecl(class._module.Node?, field$tag) == _module.Node.tag
   && !$IsGhostField(_module.Node.tag);
}

const _module.Node.score: Field
uses {
axiom FDim(_module.Node.score) == 0
   && FieldOfDecl(class._module.Node?, field$score) == _module.Node.score
   && !$IsGhostField(_module.Node.score);
}

const _module.Node.rank: Field
uses {
axiom FDim(_module.Node.rank) == 0
   && FieldOfDecl(class._module.Node?, field$rank) == _module.Node.rank
   && !$IsGhostField(_module.Node.rank);
}

procedure {:verboseName "Node._ctor (well-formedness)"} CheckWellFormed$$_module.Node.__ctor(v#0: int, t#0: int, s#0: int, r#0: int) returns (this: ref);
  modifies $Heap, $Alloc;



procedure {:verboseName "Node._ctor (call)"} Call$$_module.Node.__ctor(v#0: int, t#0: int, s#0: int, r#0: int)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && (this == null || $Alloc[this]));
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id2182"} $Unbox(read($Heap, this, _module.Node.val)): int == v#0;
  free ensures {:always_assume} true;
  ensures {:id "id2183"} $Unbox(read($Heap, this, _module.Node.tag)): int == t#0;
  free ensures {:always_assume} true;
  ensures {:id "id2184"} $Unbox(read($Heap, this, _module.Node.score)): int == s#0;
  free ensures {:always_assume} true;
  ensures {:id "id2185"} $Unbox(read($Heap, this, _module.Node.rank)): int == r#0;
  // constructor allocates the object
  ensures !old($Alloc)[this];



procedure {:verboseName "Node._ctor (correctness)"} Impl$$_module.Node.__ctor(v#0: int, t#0: int, s#0: int, r#0: int)
   returns (this: ref, $_reverifyPost: bool);
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id2186"} $Unbox(read($Heap, this, _module.Node.val)): int == v#0;
  free ensures {:always_assume} true;
  ensures {:id "id2187"} $Unbox(read($Heap, this, _module.Node.tag)): int == t#0;
  free ensures {:always_assume} true;
  ensures {:id "id2188"} $Unbox(read($Heap, this, _module.Node.score)): int == s#0;
  free ensures {:always_assume} true;
  ensures {:id "id2189"} $Unbox(read($Heap, this, _module.Node.rank)): int == r#0;



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
  $IsBox(bx, Tclass._module.Node?()) ==> $Box($Unbox(bx): ref) == bx);

implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Node._ctor (correctness)"} Impl$$_module.Node.__ctor(v#0: int, t#0: int, s#0: int, r#0: int)
   returns (this: ref, $_reverifyPost: bool)
{
  var this.val: int;
  var this.tag: int;
  var this.score: int;
  var this.rank: int;

    // AddMethodImpl: _ctor, Impl$$_module.Node.__ctor
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
    assume !$Alloc[this];
    assume $Unbox(read($Heap, this, _module.Node.val)): int == this.val;
    assume $Unbox(read($Heap, this, _module.Node.tag)): int == this.tag;
    assume $Unbox(read($Heap, this, _module.Node.score)): int == this.score;
    assume $Unbox(read($Heap, this, _module.Node.rank)): int == this.rank;
    $Alloc := $Alloc[this := true];
    assume true;
    // ----- divided block after new; ----- /Users/saline/development/projects/dafny/Test/arith.dfy(10,3)
}



// $Is axiom for non-null type _module.Node
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Node()) } { $Is(c#0, Tclass._module.Node?()) } 
  $Is(c#0, Tclass._module.Node())
     <==> $Is(c#0, Tclass._module.Node?()) && c#0 != null);

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
