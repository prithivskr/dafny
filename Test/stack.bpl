
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

const unique class._module.Stack?: ClassName;

const _module.Stack.data: Field
uses {
axiom FDim(_module.Stack.data) == 0
   && FieldOfDecl(class._module.Stack?, field$data) == _module.Stack.data
   && !$IsGhostField(_module.Stack.data);
}

const _module.Stack.top: Field
uses {
axiom FDim(_module.Stack.top) == 0
   && FieldOfDecl(class._module.Stack?, field$top) == _module.Stack.top
   && !$IsGhostField(_module.Stack.top);
}

// function declaration for _module.Stack.Valid
function _module.Stack.Valid($heap: Heap, this: ref) : bool;

function _module.Stack.Valid#canCall($heap: Heap, this: ref) : bool;

function Tclass._module.Stack() : Ty
uses {
// Tclass._module.Stack Tag
axiom Tag(Tclass._module.Stack()) == Tagclass._module.Stack
   && TagFamily(Tclass._module.Stack()) == tytagFamily$Stack;
}

const unique Tagclass._module.Stack: TyTag;

// Box/unbox axiom for Tclass._module.Stack
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Stack()) } 
  $IsBox(bx, Tclass._module.Stack()) ==> $Box($Unbox(bx): ref) == bx);

// frame axiom for _module.Stack.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Stack.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Stack())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall $o: ref, $f: Field :: 
      $o != null
           && ($o == this || $o == $Unbox(read($h0, this, _module.Stack.data)): ref)
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Stack.Valid($h0, this) == _module.Stack.Valid($h1, this)
       && _module.Stack.Valid#canCall($h0, this) == _module.Stack.Valid#canCall($h1, this));

function _module.Stack.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.Stack.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.Stack.Valid#requires($Heap, this) } 
  $IsGoodHeap($Heap) && this != null && $Is(this, Tclass._module.Stack())
     ==> _module.Stack.Valid#requires($Heap, this) == true);

// #requires ==> #canCall for _module.Stack.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.Stack.Valid#requires($Heap, this) } 
  _module.Stack.Valid#requires($Heap, this)
     ==> _module.Stack.Valid#canCall($Heap, this));

// definition axiom for _module.Stack.Valid (revealed)
axiom {:id "id0"} (forall $Heap: Heap, this: ref :: 
  { _module.Stack.Valid($Heap, this) } 
  _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       == ($Unbox(read($Heap, this, _module.Stack.data)): ref != null
         && 
        LitInt(0) <= $Unbox(read($Heap, this, _module.Stack.top)): int
         && $Unbox(read($Heap, this, _module.Stack.top)): int
           <= _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref)));

procedure {:verboseName "Stack.Valid (well-formedness)"} CheckWellformed$$_module.Stack.Valid(this: ref where this != null && $Is(this, Tclass._module.Stack()));
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Stack.Valid (well-formedness)"} CheckWellformed$$_module.Stack.Valid(this: ref)
{
  var $_ReadsFrame: [ref,Field]bool;
  var b$reqreads#0: bool;
  var newtype$check#0: ref;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;
  var b$reqreads#4: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;
    b$reqreads#4 := true;

    assume {:captureState "Test/stack.dfy(5,12): initial state"} true;
    $_ReadsFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Alloc[$o]
         ==> $o == this || $o == $Unbox(read($Heap, this, _module.Stack.data)): ref);
    // Check well-formedness of preconditions, and then assume them
    // Check well-formedness of the reads clause
    b$reqreads#0 := $_ReadsFrame[this, _module.Stack.data];
    assume true;
    assert {:id "id1"} b$reqreads#0;
    // Check well-formedness of the decreases clause
    assume true;
    // Check body and ensures clauses
    if (*)
    {
        // Check well-formedness of postcondition and assume false
        assume false;
    }
    else
    {
        // Check well-formedness of body and result subset type constraint
        b$reqreads#1 := $_ReadsFrame[this, _module.Stack.data];
        assume true;
        newtype$check#0 := null;
        if ($Unbox(read($Heap, this, _module.Stack.data)): ref != null)
        {
            b$reqreads#2 := $_ReadsFrame[this, _module.Stack.top];
            assume true;
            if (LitInt(0) <= $Unbox(read($Heap, this, _module.Stack.top)): int)
            {
                b$reqreads#3 := $_ReadsFrame[this, _module.Stack.top];
                assume true;
                b$reqreads#4 := $_ReadsFrame[this, _module.Stack.data];
                assume true;
                assert {:id "id2"} $Unbox(read($Heap, this, _module.Stack.data)): ref != null;
                assume true;
            }
        }

        assume true;
        assume {:id "id3"} _module.Stack.Valid($Heap, this)
           == ($Unbox(read($Heap, this, _module.Stack.data)): ref != null
             && 
            LitInt(0) <= $Unbox(read($Heap, this, _module.Stack.top)): int
             && $Unbox(read($Heap, this, _module.Stack.top)): int
               <= _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Stack.Valid($Heap, this), TBool);
        assert {:id "id4"} b$reqreads#1;
        assert {:id "id5"} b$reqreads#2;
        assert {:id "id6"} b$reqreads#3;
        assert {:id "id7"} b$reqreads#4;
        return;

        assume false;
    }
}



procedure {:verboseName "Stack.Init (well-formedness)"} CheckWellFormed$$_module.Stack.Init(capacity#0: int) returns (this: ref);
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Stack.Init (well-formedness)"} CheckWellFormed$$_module.Stack.Init(capacity#0: int) returns (this: ref)
{

    // AddMethodImpl: Init, CheckWellFormed$$_module.Stack.Init
    assume {:captureState "Test/stack.dfy(12,14): initial state"} true;
    assume {:id "id8"} capacity#0 > 0;
    havoc $Heap;
    havoc this;
    assume this != null
       && 
      $Is(this, Tclass._module.Stack())
       && (this == null || $Alloc[this]);
    assume {:captureState "Test/stack.dfy(14,17): post-state"} true;
    // assume allocatedness for receiver argument to function
    assume $Unbox($Box(this)): ref == null || $Alloc[$Unbox($Box(this)): ref];
    assume _module.Stack.Valid#canCall($Heap, this);
    assume {:id "id9"} _module.Stack.Valid($Heap, this);
    assume true;
    assume {:id "id10"} $Unbox(read($Heap, this, _module.Stack.top)): int == LitInt(0);
    assume true;
    assert {:id "id11"} $Unbox(read($Heap, this, _module.Stack.data)): ref != null;
    assume true;
    assume {:id "id12"} _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref)
       == capacity#0;
}



procedure {:verboseName "Stack.Init (call)"} Call$$_module.Stack.Init(capacity#0: int)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Stack())
         && (this == null || $Alloc[this]));
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id13"} capacity#0 > 0;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} _module.Stack.Valid#canCall($Heap, this);
  free ensures {:id "id14"} _module.Stack.Valid#canCall($Heap, this)
     && 
    _module.Stack.Valid($Heap, this)
     && 
    $Unbox(read($Heap, this, _module.Stack.data)): ref != null
     && 
    LitInt(0) <= $Unbox(read($Heap, this, _module.Stack.top)): int
     && $Unbox(read($Heap, this, _module.Stack.top)): int
       <= _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
  free ensures {:always_assume} true;
  ensures {:id "id15"} $Unbox(read($Heap, this, _module.Stack.top)): int == LitInt(0);
  free ensures {:always_assume} true;
  ensures {:id "id16"} _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref)
     == capacity#0;
  // constructor allocates the object
  ensures !old($Alloc)[this];



procedure {:verboseName "Stack.Init (correctness)"} Impl$$_module.Stack.Init(capacity#0: int) returns (this: ref, $_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id17"} capacity#0 > 0;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} _module.Stack.Valid#canCall($Heap, this);
  ensures {:id "id18"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || $Unbox(read($Heap, this, _module.Stack.data)): ref != null;
  ensures {:id "id19"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || LitInt(0) <= $Unbox(read($Heap, this, _module.Stack.top)): int;
  ensures {:id "id20"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || $Unbox(read($Heap, this, _module.Stack.top)): int
         <= _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
  free ensures {:always_assume} true;
  ensures {:id "id21"} $Unbox(read($Heap, this, _module.Stack.top)): int == LitInt(0);
  free ensures {:always_assume} true;
  ensures {:id "id22"} _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref)
     == capacity#0;



function Tclass._module.Stack?() : Ty
uses {
// Tclass._module.Stack? Tag
axiom Tag(Tclass._module.Stack?()) == Tagclass._module.Stack?
   && TagFamily(Tclass._module.Stack?()) == tytagFamily$Stack;
}

const unique Tagclass._module.Stack?: TyTag;

// Box/unbox axiom for Tclass._module.Stack?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Stack?()) } 
  $IsBox(bx, Tclass._module.Stack?()) ==> $Box($Unbox(bx): ref) == bx);

implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Stack.Init (correctness)"} Impl$$_module.Stack.Init(capacity#0: int) returns (this: ref, $_reverifyPost: bool)
{
  var this.data: ref;
  var this.top: int;
  var $nw: ref;

    // AddMethodImpl: Init, Impl$$_module.Stack.Init
    assume {:captureState "Test/stack.dfy(17,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/saline/development/projects/dafny/Test/stack.dfy(17,3)
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/stack.dfy(18,10)
    assume true;
    assume true;
    assert {:id "id23"} 0 <= capacity#0;
    havoc $nw;
    assume $nw != null && $Is($nw, Tclass._System.array?(TInt));
    assume !$Alloc[$nw];
    assume _System.array.Length($nw) == capacity#0;
    $Alloc := $Alloc[$nw := true];
    assume true;
    this.data := $nw;
    assume {:captureState "Test/stack.dfy(18,29)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/stack.dfy(19,9)
    assume true;
    assume true;
    assume true;
    this.top := LitInt(0);
    assume {:captureState "Test/stack.dfy(19,12)"} true;
    // ----- new; ----- /Users/saline/development/projects/dafny/Test/stack.dfy(17,3)
    assume this != null && $Is(this, Tclass._module.Stack?());
    assume !$Alloc[this];
    assume $Unbox(read($Heap, this, _module.Stack.data)): ref == this.data;
    assume $Unbox(read($Heap, this, _module.Stack.top)): int == this.top;
    $Alloc := $Alloc[this := true];
    assume true;
    // ----- divided block after new; ----- /Users/saline/development/projects/dafny/Test/stack.dfy(17,3)
}



procedure {:verboseName "Stack.Push (well-formedness)"} CheckWellFormed$$_module.Stack.Push(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Stack())
         && (this == null || $Alloc[this]), 
    x#0: int);
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Stack.Push (well-formedness)"} CheckWellFormed$$_module.Stack.Push(this: ref, x#0: int)
{

    // AddMethodImpl: Push, CheckWellFormed$$_module.Stack.Push
    assume {:captureState "Test/stack.dfy(22,9): initial state"} true;
    // assume allocatedness for receiver argument to function
    assume $Unbox($Box(this)): ref == null || $Alloc[$Unbox($Box(this)): ref];
    assume _module.Stack.Valid#canCall($Heap, this);
    assume {:id "id26"} _module.Stack.Valid($Heap, this);
    assume true;
    assume true;
    assert {:id "id27"} $Unbox(read($Heap, this, _module.Stack.data)): ref != null;
    assume true;
    assume {:id "id28"} $Unbox(read($Heap, this, _module.Stack.top)): int
       < _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
    assume true;
    havoc $Heap;
    assume {:captureState "Test/stack.dfy(26,17): post-state"} true;
    // assume allocatedness for receiver argument to function
    assume $Unbox($Box(this)): ref == null || $Alloc[$Unbox($Box(this)): ref];
    assume _module.Stack.Valid#canCall($Heap, this);
    assume {:id "id29"} _module.Stack.Valid($Heap, this);
    assume true;
    assert {:id "id30"} this == null || old($Alloc)[this];
    assume true;
    assume {:id "id31"} $Unbox(read($Heap, this, _module.Stack.top)): int
       == $Unbox(read(old($Heap), this, _module.Stack.top)): int + 1;
    assume true;
    assert {:id "id32"} $Unbox(read($Heap, this, _module.Stack.data)): ref != null;
    assume true;
    assert {:id "id33"} 0 <= $Unbox(read($Heap, this, _module.Stack.top)): int - 1
       && $Unbox(read($Heap, this, _module.Stack.top)): int - 1
         < _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
    assume {:id "id34"} $Unbox(read($Heap, 
          $Unbox(read($Heap, this, _module.Stack.data)): ref, 
          IndexField($Unbox(read($Heap, this, _module.Stack.top)): int - 1))): int
       == x#0;
}



procedure {:verboseName "Stack.Push (call)"} Call$$_module.Stack.Push(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Stack())
         && (this == null || $Alloc[this]), 
    x#0: int);
  // user-defined preconditions
  free requires {:always_assume} _module.Stack.Valid#canCall($Heap, this);
  requires {:id "id35"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || $Unbox(read($Heap, this, _module.Stack.data)): ref != null;
  requires {:id "id36"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || LitInt(0) <= $Unbox(read($Heap, this, _module.Stack.top)): int;
  requires {:id "id37"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || $Unbox(read($Heap, this, _module.Stack.top)): int
         <= _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
  free requires {:always_assume} true;
  requires {:id "id38"} $Unbox(read($Heap, this, _module.Stack.top)): int
     < _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} _module.Stack.Valid#canCall($Heap, this);
  free ensures {:id "id39"} _module.Stack.Valid#canCall($Heap, this)
     && 
    _module.Stack.Valid($Heap, this)
     && 
    $Unbox(read($Heap, this, _module.Stack.data)): ref != null
     && 
    LitInt(0) <= $Unbox(read($Heap, this, _module.Stack.top)): int
     && $Unbox(read($Heap, this, _module.Stack.top)): int
       <= _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
  free ensures {:always_assume} true;
  ensures {:id "id40"} $Unbox(read($Heap, this, _module.Stack.top)): int
     == $Unbox(read(old($Heap), this, _module.Stack.top)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id41"} $Unbox(read($Heap, 
        $Unbox(read($Heap, this, _module.Stack.data)): ref, 
        IndexField($Unbox(read($Heap, this, _module.Stack.top)): int - 1))): int
     == x#0;



procedure {:verboseName "Stack.Push (correctness)"} Impl$$_module.Stack.Push(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Stack())
         && (this == null || $Alloc[this]), 
    x#0: int)
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} _module.Stack.Valid#canCall($Heap, this);
  free requires {:id "id42"} _module.Stack.Valid#canCall($Heap, this)
     && 
    _module.Stack.Valid($Heap, this)
     && 
    $Unbox(read($Heap, this, _module.Stack.data)): ref != null
     && 
    LitInt(0) <= $Unbox(read($Heap, this, _module.Stack.top)): int
     && $Unbox(read($Heap, this, _module.Stack.top)): int
       <= _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
  free requires {:always_assume} true;
  requires {:id "id43"} $Unbox(read($Heap, this, _module.Stack.top)): int
     < _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} _module.Stack.Valid#canCall($Heap, this);
  ensures {:id "id44"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || $Unbox(read($Heap, this, _module.Stack.data)): ref != null;
  ensures {:id "id45"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || LitInt(0) <= $Unbox(read($Heap, this, _module.Stack.top)): int;
  ensures {:id "id46"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || $Unbox(read($Heap, this, _module.Stack.top)): int
         <= _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
  free ensures {:always_assume} true;
  ensures {:id "id47"} $Unbox(read($Heap, this, _module.Stack.top)): int
     == $Unbox(read(old($Heap), this, _module.Stack.top)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id48"} $Unbox(read($Heap, 
        $Unbox(read($Heap, this, _module.Stack.data)): ref, 
        IndexField($Unbox(read($Heap, this, _module.Stack.top)): int - 1))): int
     == x#0;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Stack.Push (correctness)"} Impl$$_module.Stack.Push(this: ref, x#0: int) returns ($_reverifyPost: bool)
{
  var $rhs#0: int;
  var $rhs#1: int;

    // AddMethodImpl: Push, Impl$$_module.Stack.Push
    assume {:captureState "Test/stack.dfy(29,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/stack.dfy(30,15)
    assume true;
    assert {:id "id49"} $Unbox(read($Heap, this, _module.Stack.data)): ref != null;
    assume true;
    assert {:id "id50"} 0 <= $Unbox(read($Heap, this, _module.Stack.top)): int
       && $Unbox(read($Heap, this, _module.Stack.top)): int
         < _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
    assume true;
    assume true;
    $rhs#0 := x#0;
    $Heap := update($Heap, 
      $Unbox(read($Heap, this, _module.Stack.data)): ref, 
      IndexField($Unbox(read($Heap, this, _module.Stack.top)): int), 
      $Box($rhs#0));
    assume true;
    assume {:captureState "Test/stack.dfy(30,18)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/stack.dfy(31,9)
    assume true;
    assume true;
    assume true;
    assume true;
    $rhs#1 := $Unbox(read($Heap, this, _module.Stack.top)): int + 1;
    $Heap := update($Heap, this, _module.Stack.top, $Box($rhs#1));
    assume true;
    assume {:captureState "Test/stack.dfy(31,18)"} true;
}



procedure {:verboseName "Stack.Pop (well-formedness)"} CheckWellFormed$$_module.Stack.Pop(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Stack())
         && (this == null || $Alloc[this]))
   returns (x#0: int);
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Stack.Pop (well-formedness)"} CheckWellFormed$$_module.Stack.Pop(this: ref) returns (x#0: int)
{

    // AddMethodImpl: Pop, CheckWellFormed$$_module.Stack.Pop
    assume {:captureState "Test/stack.dfy(34,9): initial state"} true;
    // assume allocatedness for receiver argument to function
    assume $Unbox($Box(this)): ref == null || $Alloc[$Unbox($Box(this)): ref];
    assume _module.Stack.Valid#canCall($Heap, this);
    assume {:id "id55"} _module.Stack.Valid($Heap, this);
    assume true;
    assume {:id "id56"} $Unbox(read($Heap, this, _module.Stack.top)): int > 0;
    havoc $Heap;
    havoc x#0;
    assume {:captureState "Test/stack.dfy(38,17): post-state"} true;
    // assume allocatedness for receiver argument to function
    assume $Unbox($Box(this)): ref == null || $Alloc[$Unbox($Box(this)): ref];
    assume _module.Stack.Valid#canCall($Heap, this);
    assume {:id "id57"} _module.Stack.Valid($Heap, this);
    assume true;
    assert {:id "id58"} this == null || old($Alloc)[this];
    assume true;
    assume {:id "id59"} $Unbox(read($Heap, this, _module.Stack.top)): int
       == $Unbox(read(old($Heap), this, _module.Stack.top)): int - 1;
    assert {:id "id60"} this == null || old($Alloc)[this];
    assume true;
    assert {:id "id61"} $Unbox(read(old($Heap), this, _module.Stack.data)): ref != null;
    assert {:id "id62"} $Unbox(read(old($Heap), this, _module.Stack.data)): ref == null
       || old($Alloc)[$Unbox(read(old($Heap), this, _module.Stack.data)): ref];
    assert {:id "id63"} this == null || old($Alloc)[this];
    assume true;
    assert {:id "id64"} 0 <= $Unbox(read(old($Heap), this, _module.Stack.top)): int - 1
       && $Unbox(read(old($Heap), this, _module.Stack.top)): int - 1
         < _System.array.Length($Unbox(read(old($Heap), this, _module.Stack.data)): ref);
    assume {:id "id65"} x#0
       == $Unbox(read(old($Heap), 
          $Unbox(read(old($Heap), this, _module.Stack.data)): ref, 
          IndexField($Unbox(read(old($Heap), this, _module.Stack.top)): int - 1))): int;
}



procedure {:verboseName "Stack.Pop (call)"} Call$$_module.Stack.Pop(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Stack())
         && (this == null || $Alloc[this]))
   returns (x#0: int);
  // user-defined preconditions
  free requires {:always_assume} _module.Stack.Valid#canCall($Heap, this);
  requires {:id "id66"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || $Unbox(read($Heap, this, _module.Stack.data)): ref != null;
  requires {:id "id67"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || LitInt(0) <= $Unbox(read($Heap, this, _module.Stack.top)): int;
  requires {:id "id68"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || $Unbox(read($Heap, this, _module.Stack.top)): int
         <= _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
  free requires {:always_assume} true;
  requires {:id "id69"} $Unbox(read($Heap, this, _module.Stack.top)): int > 0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} _module.Stack.Valid#canCall($Heap, this);
  free ensures {:id "id70"} _module.Stack.Valid#canCall($Heap, this)
     && 
    _module.Stack.Valid($Heap, this)
     && 
    $Unbox(read($Heap, this, _module.Stack.data)): ref != null
     && 
    LitInt(0) <= $Unbox(read($Heap, this, _module.Stack.top)): int
     && $Unbox(read($Heap, this, _module.Stack.top)): int
       <= _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
  free ensures {:always_assume} true;
  ensures {:id "id71"} $Unbox(read($Heap, this, _module.Stack.top)): int
     == $Unbox(read(old($Heap), this, _module.Stack.top)): int - 1;
  free ensures {:always_assume} true;
  ensures {:id "id72"} x#0
     == $Unbox(read(old($Heap), 
        $Unbox(read(old($Heap), this, _module.Stack.data)): ref, 
        IndexField($Unbox(read(old($Heap), this, _module.Stack.top)): int - 1))): int;



procedure {:verboseName "Stack.Pop (correctness)"} Impl$$_module.Stack.Pop(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Stack())
         && (this == null || $Alloc[this]))
   returns (defass#x#0: bool, x#0: int, $_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} _module.Stack.Valid#canCall($Heap, this);
  free requires {:id "id73"} _module.Stack.Valid#canCall($Heap, this)
     && 
    _module.Stack.Valid($Heap, this)
     && 
    $Unbox(read($Heap, this, _module.Stack.data)): ref != null
     && 
    LitInt(0) <= $Unbox(read($Heap, this, _module.Stack.top)): int
     && $Unbox(read($Heap, this, _module.Stack.top)): int
       <= _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
  free requires {:always_assume} true;
  requires {:id "id74"} $Unbox(read($Heap, this, _module.Stack.top)): int > 0;
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} _module.Stack.Valid#canCall($Heap, this);
  ensures {:id "id75"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || $Unbox(read($Heap, this, _module.Stack.data)): ref != null;
  ensures {:id "id76"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || LitInt(0) <= $Unbox(read($Heap, this, _module.Stack.top)): int;
  ensures {:id "id77"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || $Unbox(read($Heap, this, _module.Stack.top)): int
         <= _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
  free ensures {:always_assume} true;
  ensures {:id "id78"} $Unbox(read($Heap, this, _module.Stack.top)): int
     == $Unbox(read(old($Heap), this, _module.Stack.top)): int - 1;
  free ensures {:always_assume} true;
  ensures {:id "id79"} x#0
     == $Unbox(read(old($Heap), 
        $Unbox(read(old($Heap), this, _module.Stack.data)): ref, 
        IndexField($Unbox(read(old($Heap), this, _module.Stack.top)): int - 1))): int;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Stack.Pop (correctness)"} Impl$$_module.Stack.Pop(this: ref) returns (defass#x#0: bool, x#0: int, $_reverifyPost: bool)
{
  var $rhs#0: int;

    // AddMethodImpl: Pop, Impl$$_module.Stack.Pop
    assume {:captureState "Test/stack.dfy(41,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/stack.dfy(42,9)
    assume true;
    assume true;
    assume true;
    assume true;
    $rhs#0 := $Unbox(read($Heap, this, _module.Stack.top)): int - 1;
    $Heap := update($Heap, this, _module.Stack.top, $Box($rhs#0));
    assume true;
    assume {:captureState "Test/stack.dfy(42,18)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/stack.dfy(43,7)
    assume true;
    assume true;
    assert {:id "id82"} $Unbox(read($Heap, this, _module.Stack.data)): ref != null;
    assume true;
    assert {:id "id83"} 0 <= $Unbox(read($Heap, this, _module.Stack.top)): int
       && $Unbox(read($Heap, this, _module.Stack.top)): int
         < _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
    assume true;
    x#0 := $Unbox(read($Heap, 
        $Unbox(read($Heap, this, _module.Stack.data)): ref, 
        IndexField($Unbox(read($Heap, this, _module.Stack.top)): int))): int;
    defass#x#0 := true;
    assume {:captureState "Test/stack.dfy(43,18)"} true;
    assert {:id "id85"} defass#x#0;
}



procedure {:verboseName "Stack.Size (well-formedness)"} CheckWellFormed$$_module.Stack.Size(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Stack())
         && (this == null || $Alloc[this]))
   returns (n#0: int);
  modifies $Heap, $Alloc;



procedure {:verboseName "Stack.Size (call)"} Call$$_module.Stack.Size(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Stack())
         && (this == null || $Alloc[this]))
   returns (n#0: int);
  // user-defined preconditions
  free requires {:always_assume} _module.Stack.Valid#canCall($Heap, this);
  requires {:id "id88"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || $Unbox(read($Heap, this, _module.Stack.data)): ref != null;
  requires {:id "id89"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || LitInt(0) <= $Unbox(read($Heap, this, _module.Stack.top)): int;
  requires {:id "id90"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || $Unbox(read($Heap, this, _module.Stack.top)): int
         <= _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id91"} n#0 == $Unbox(read($Heap, this, _module.Stack.top)): int;



procedure {:verboseName "Stack.Size (correctness)"} Impl$$_module.Stack.Size(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Stack())
         && (this == null || $Alloc[this]))
   returns (defass#n#0: bool, n#0: int, $_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} _module.Stack.Valid#canCall($Heap, this);
  free requires {:id "id92"} _module.Stack.Valid#canCall($Heap, this)
     && 
    _module.Stack.Valid($Heap, this)
     && 
    $Unbox(read($Heap, this, _module.Stack.data)): ref != null
     && 
    LitInt(0) <= $Unbox(read($Heap, this, _module.Stack.top)): int
     && $Unbox(read($Heap, this, _module.Stack.top)): int
       <= _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id93"} n#0 == $Unbox(read($Heap, this, _module.Stack.top)): int;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Stack.Size (correctness)"} Impl$$_module.Stack.Size(this: ref) returns (defass#n#0: bool, n#0: int, $_reverifyPost: bool)
{
    // AddMethodImpl: Size, Impl$$_module.Stack.Size
    assume {:captureState "Test/stack.dfy(49,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/stack.dfy(50,7)
    assume true;
    assume true;
    assume true;
    n#0 := $Unbox(read($Heap, this, _module.Stack.top)): int;
    defass#n#0 := true;
    assume {:captureState "Test/stack.dfy(50,12)"} true;
    assert {:id "id95"} defass#n#0;
}



procedure {:verboseName "Stack.IsEmpty (well-formedness)"} CheckWellFormed$$_module.Stack.IsEmpty(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Stack())
         && (this == null || $Alloc[this]))
   returns (b#0: bool);
  modifies $Heap, $Alloc;



procedure {:verboseName "Stack.IsEmpty (call)"} Call$$_module.Stack.IsEmpty(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Stack())
         && (this == null || $Alloc[this]))
   returns (b#0: bool);
  // user-defined preconditions
  free requires {:always_assume} _module.Stack.Valid#canCall($Heap, this);
  requires {:id "id98"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || $Unbox(read($Heap, this, _module.Stack.data)): ref != null;
  requires {:id "id99"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || LitInt(0) <= $Unbox(read($Heap, this, _module.Stack.top)): int;
  requires {:id "id100"} _module.Stack.Valid#canCall($Heap, this)
     ==> _module.Stack.Valid($Heap, this)
       || $Unbox(read($Heap, this, _module.Stack.top)): int
         <= _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id101"} b#0 <==> $Unbox(read($Heap, this, _module.Stack.top)): int == LitInt(0);



procedure {:verboseName "Stack.IsEmpty (correctness)"} Impl$$_module.Stack.IsEmpty(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Stack())
         && (this == null || $Alloc[this]))
   returns (defass#b#0: bool, b#0: bool, $_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} _module.Stack.Valid#canCall($Heap, this);
  free requires {:id "id102"} _module.Stack.Valid#canCall($Heap, this)
     && 
    _module.Stack.Valid($Heap, this)
     && 
    $Unbox(read($Heap, this, _module.Stack.data)): ref != null
     && 
    LitInt(0) <= $Unbox(read($Heap, this, _module.Stack.top)): int
     && $Unbox(read($Heap, this, _module.Stack.top)): int
       <= _System.array.Length($Unbox(read($Heap, this, _module.Stack.data)): ref);
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id103"} b#0 <==> $Unbox(read($Heap, this, _module.Stack.top)): int == LitInt(0);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Stack.IsEmpty (correctness)"} Impl$$_module.Stack.IsEmpty(this: ref) returns (defass#b#0: bool, b#0: bool, $_reverifyPost: bool)
{
    // AddMethodImpl: IsEmpty, Impl$$_module.Stack.IsEmpty
    assume {:captureState "Test/stack.dfy(56,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/stack.dfy(57,7)
    assume true;
    assume true;
    assume true;
    b#0 := $Unbox(read($Heap, this, _module.Stack.top)): int == LitInt(0);
    defass#b#0 := true;
    assume {:captureState "Test/stack.dfy(57,17)"} true;
    assert {:id "id105"} defass#b#0;
}



// $Is axiom for non-null type _module.Stack
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Stack()) } { $Is(c#0, Tclass._module.Stack?()) } 
  $Is(c#0, Tclass._module.Stack())
     <==> $Is(c#0, Tclass._module.Stack?()) && c#0 != null);

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

const unique tytagFamily$Stack: TyTagFamily;

const unique field$data: NameFamily;

const unique field$top: NameFamily;
