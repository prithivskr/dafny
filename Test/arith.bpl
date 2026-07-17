
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

axiom (forall t: Ty :: { TSet(t) } Inv0_TSet(TSet(t)) == t);

axiom (forall t: Ty :: { TSet(t) } Tag(TSet(t)) == TagSet);

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

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TSet(t)) } 
  $IsBox(bx, TSet(t))
     ==> $Box($Unbox(bx): Set) == bx && $Is($Unbox(bx): Set, TSet(t)));

axiom (forall<T> v: T, t: Ty :: 
  { $IsBox($Box(v), t) } 
  $IsBox($Box(v), t) <==> $Is(v, t));

revealed function $Is<T>(T, Ty) : bool;

revealed function $IsAlloc<T>(T, Ty, Heap) : bool;

revealed function $AlwaysAllocated(Ty) : bool;

revealed function $OlderTag(Heap) : bool;

axiom (forall v: Set, t0: Ty :: 
  { $Is(v, TSet(t0)) } 
  $Is(v, TSet(t0))
     <==> (forall bx: Box :: 
      { Set#IsMember(v, bx) } 
      Set#IsMember(v, bx) ==> $IsBox(bx, t0)));

axiom (forall v: Set, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TSet(t0), h) } 
  $IsAlloc(v, TSet(t0), h)
     <==> (forall bx: Box :: 
      { Set#IsMember(v, bx) } 
      Set#IsMember(v, bx) ==> $IsAllocBox(bx, t0, h)));

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



type Set = [Box]bool;

revealed function {:inline} Set#IsMember(s: Set, o: Box) : bool
{
  s[o]
}

revealed function {:inline} Set#Empty() : Set
{
  (lambda o: Box :: false)
}

revealed function {:inline} Set#UnionOne(s: Set, x: Box) : Set
{
  s[x := true]
}

revealed function {:inline} Set#Union(a: Set, b: Set) : Set
{
  (lambda o: Box :: a[o] || b[o])
}

revealed function {:inline} Set#Intersection(a: Set, b: Set) : Set
{
  (lambda o: Box :: a[o] && b[o])
}

revealed function {:inline} Set#Difference(a: Set, b: Set) : Set
{
  (lambda o: Box :: a[o] && !b[o])
}

revealed function {:inline} Set#Equal(a: Set, b: Set) : bool
{
  a == b
}

revealed function Set#Subset(a: Set, b: Set) : bool;

axiom (forall a: Set, b: Set :: 
  { Set#Subset(a, b) } 
  Set#Subset(a, b) <==> (forall o: Box :: { a[o] } { b[o] } a[o] ==> b[o]));

revealed function Set#Disjoint(a: Set, b: Set) : bool;

axiom (forall a: Set, b: Set :: 
  { Set#Disjoint(a, b) } 
  Set#Disjoint(a, b) <==> (forall o: Box :: !a[o] || !b[o]));

axiom (forall s: Set :: 
  { Set#Equal(s, Set#Empty()) } 
  !Set#Equal(s, Set#Empty())
     ==> (exists x: Box :: { Set#IsMember(s, x) } Set#IsMember(s, x)));

revealed function {:inline} Set#FromBoogieMap(m: [Box]bool) : Set
{
  m
}

revealed function Set#Card(s: Set) : int;

axiom (forall s: Set :: { Set#Card(s) } 0 <= Set#Card(s));

axiom (forall s: Set :: 
  { Set#Card(s) } 
  (Set#Card(s) == 0 <==> s == Set#Empty())
     && (Set#Card(s) != 0 ==> (exists x: Box :: s[x])));

axiom (forall a: Set, x: Box :: 
  { Set#Card(a[x := true]) } 
  a[x] ==> Set#Card(a[x := true]) == Set#Card(a));

axiom (forall a: Set, x: Box :: 
  { Set#Card(a[x := true]) } 
  !a[x] ==> Set#Card(a[x := true]) == Set#Card(a) + 1);

axiom (forall a: Set, b: Set :: 
  { Set#Card(Set#Union(a, b)) } { Set#Card(Set#Intersection(a, b)) } 
  Set#Card(Set#Union(a, b)) + Set#Card(Set#Intersection(a, b))
     == Set#Card(a) + Set#Card(b));

axiom (forall a: Set, b: Set :: 
  { Set#Card(Set#Difference(a, b)) } 
  Set#Card(Set#Difference(a, b))
         + Set#Card(Set#Difference(b, a))
         + Set#Card(Set#Intersection(a, b))
       == Set#Card(Set#Union(a, b))
     && Set#Card(Set#Difference(a, b)) == Set#Card(a) - Set#Card(Set#Intersection(a, b)));

axiom (forall a: Set, b: Set :: 
  { Set#Subset(a, b), Set#Card(a), Set#Card(b) } 
  Set#Subset(a, b) && !Set#Subset(b, a) ==> Set#Card(a) < Set#Card(b));

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
    assume {:captureState "Test/arith.dfy(11,7): initial state"} true;
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
    assume {:captureState "Test/arith.dfy(17,57): post-state"} true;
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
    assert {:id "id27"} b#0 != null;
    assume true;
    assert {:id "id28"} b#0 != null;
    assert {:id "id29"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id30"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 1;
    assert {:id "id31"} b#0 != null;
    assume true;
    assert {:id "id32"} b#0 != null;
    assert {:id "id33"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id34"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id35"} b#0 != null;
    assume true;
    assert {:id "id36"} b#0 != null;
    assert {:id "id37"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id38"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id39"} c#0 != null;
    assume true;
    assert {:id "id40"} c#0 != null;
    assert {:id "id41"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id42"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 1;
    assert {:id "id43"} c#0 != null;
    assume true;
    assert {:id "id44"} c#0 != null;
    assert {:id "id45"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id46"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id47"} c#0 != null;
    assume true;
    assert {:id "id48"} c#0 != null;
    assert {:id "id49"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id50"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id51"} d#0 != null;
    assume true;
    assert {:id "id52"} d#0 != null;
    assert {:id "id53"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id54"} $Unbox(read($Heap, d#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 1;
    assert {:id "id55"} d#0 != null;
    assume true;
    assert {:id "id56"} d#0 != null;
    assert {:id "id57"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id58"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
    assert {:id "id59"} d#0 != null;
    assume true;
    assert {:id "id60"} d#0 != null;
    assert {:id "id61"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id62"} $Unbox(read($Heap, d#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
    assert {:id "id63"} e#0 != null;
    assume true;
    assert {:id "id64"} e#0 != null;
    assert {:id "id65"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id66"} $Unbox(read($Heap, e#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 1;
    assert {:id "id67"} e#0 != null;
    assume true;
    assert {:id "id68"} e#0 != null;
    assert {:id "id69"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id70"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
    assert {:id "id71"} e#0 != null;
    assume true;
    assert {:id "id72"} e#0 != null;
    assert {:id "id73"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id74"} $Unbox(read($Heap, e#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
    assert {:id "id75"} f#0 != null;
    assume true;
    assert {:id "id76"} f#0 != null;
    assert {:id "id77"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id78"} $Unbox(read($Heap, f#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 1;
    assert {:id "id79"} f#0 != null;
    assume true;
    assert {:id "id80"} f#0 != null;
    assert {:id "id81"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id82"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
    assert {:id "id83"} f#0 != null;
    assume true;
    assert {:id "id84"} f#0 != null;
    assert {:id "id85"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id86"} $Unbox(read($Heap, f#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
}



procedure {:verboseName "Bump (call)"} Call$$_module.__default.Bump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]));
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id87"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id88"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id89"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id90"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id91"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id92"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id93"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id94"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id95"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id96"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id97"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id98"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id99"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id100"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id101"} e#0 != f#0;
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
  ensures {:id "id102"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id103"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id104"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id105"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id106"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id107"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id108"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id109"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id110"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id111"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id112"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id113"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id114"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id115"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id116"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id117"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id118"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id119"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;



procedure {:verboseName "Bump (correctness)"} Impl$$_module.__default.Bump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]))
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id120"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id121"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id122"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id123"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id124"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id125"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id126"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id127"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id128"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id129"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id130"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id131"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id132"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id133"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id134"} e#0 != f#0;
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
  ensures {:id "id135"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id136"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id137"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id138"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id139"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id140"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id141"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id142"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id143"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id144"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id145"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id146"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id147"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id148"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id149"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id150"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 1;
  free ensures {:always_assume} true;
  ensures {:id "id151"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id152"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;



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
    assume {:captureState "Test/arith.dfy(23,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(24,9)
    assert {:id "id153"} a#0 != null;
    assume true;
    assume true;
    assert {:id "id154"} a#0 != null;
    assume true;
    assume true;
    $rhs#0 := $Unbox(read($Heap, a#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, a#0, _module.Node.val, $Box($rhs#0));
    assume true;
    assume {:captureState "Test/arith.dfy(24,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(25,9)
    assert {:id "id157"} b#0 != null;
    assume true;
    assume true;
    assert {:id "id158"} b#0 != null;
    assume true;
    assume true;
    $rhs#1 := $Unbox(read($Heap, b#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, b#0, _module.Node.val, $Box($rhs#1));
    assume true;
    assume {:captureState "Test/arith.dfy(25,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(26,9)
    assert {:id "id161"} c#0 != null;
    assume true;
    assume true;
    assert {:id "id162"} c#0 != null;
    assume true;
    assume true;
    $rhs#2 := $Unbox(read($Heap, c#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, c#0, _module.Node.val, $Box($rhs#2));
    assume true;
    assume {:captureState "Test/arith.dfy(26,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(27,9)
    assert {:id "id165"} d#0 != null;
    assume true;
    assume true;
    assert {:id "id166"} d#0 != null;
    assume true;
    assume true;
    $rhs#3 := $Unbox(read($Heap, d#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, d#0, _module.Node.val, $Box($rhs#3));
    assume true;
    assume {:captureState "Test/arith.dfy(27,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(28,9)
    assert {:id "id169"} e#0 != null;
    assume true;
    assume true;
    assert {:id "id170"} e#0 != null;
    assume true;
    assume true;
    $rhs#4 := $Unbox(read($Heap, e#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, e#0, _module.Node.val, $Box($rhs#4));
    assume true;
    assume {:captureState "Test/arith.dfy(28,20)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(29,9)
    assert {:id "id173"} f#0 != null;
    assume true;
    assume true;
    assert {:id "id174"} f#0 != null;
    assume true;
    assume true;
    $rhs#5 := $Unbox(read($Heap, f#0, _module.Node.val)): int + 1;
    $Heap := update($Heap, f#0, _module.Node.val, $Box($rhs#5));
    assume true;
    assume {:captureState "Test/arith.dfy(29,20)"} true;
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
    assume {:captureState "Test/arith.dfy(32,7): initial state"} true;
    assume {:id "id177"} a#0 != b#0;
    assume {:id "id178"} a#0 != c#0;
    assume {:id "id179"} a#0 != d#0;
    assume {:id "id180"} a#0 != e#0;
    assume {:id "id181"} a#0 != f#0;
    assume {:id "id182"} b#0 != c#0;
    assume {:id "id183"} b#0 != d#0;
    assume {:id "id184"} b#0 != e#0;
    assume {:id "id185"} b#0 != f#0;
    assume {:id "id186"} c#0 != d#0;
    assume {:id "id187"} c#0 != e#0;
    assume {:id "id188"} c#0 != f#0;
    assume {:id "id189"} d#0 != e#0;
    assume {:id "id190"} d#0 != f#0;
    assume {:id "id191"} e#0 != f#0;
    havoc $Heap;
    assume {:captureState "Test/arith.dfy(38,57): post-state"} true;
    assert {:id "id192"} a#0 != null;
    assume true;
    assert {:id "id193"} a#0 != null;
    assert {:id "id194"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id195"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 2;
    assert {:id "id196"} a#0 != null;
    assume true;
    assert {:id "id197"} a#0 != null;
    assert {:id "id198"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id199"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id200"} a#0 != null;
    assume true;
    assert {:id "id201"} a#0 != null;
    assert {:id "id202"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id203"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id204"} b#0 != null;
    assume true;
    assert {:id "id205"} b#0 != null;
    assert {:id "id206"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id207"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 2;
    assert {:id "id208"} b#0 != null;
    assume true;
    assert {:id "id209"} b#0 != null;
    assert {:id "id210"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id211"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id212"} b#0 != null;
    assume true;
    assert {:id "id213"} b#0 != null;
    assert {:id "id214"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id215"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id216"} c#0 != null;
    assume true;
    assert {:id "id217"} c#0 != null;
    assert {:id "id218"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id219"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 2;
    assert {:id "id220"} c#0 != null;
    assume true;
    assert {:id "id221"} c#0 != null;
    assert {:id "id222"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id223"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id224"} c#0 != null;
    assume true;
    assert {:id "id225"} c#0 != null;
    assert {:id "id226"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id227"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id228"} d#0 != null;
    assume true;
    assert {:id "id229"} d#0 != null;
    assert {:id "id230"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id231"} $Unbox(read($Heap, d#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 2;
    assert {:id "id232"} d#0 != null;
    assume true;
    assert {:id "id233"} d#0 != null;
    assert {:id "id234"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id235"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
    assert {:id "id236"} d#0 != null;
    assume true;
    assert {:id "id237"} d#0 != null;
    assert {:id "id238"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id239"} $Unbox(read($Heap, d#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
    assert {:id "id240"} e#0 != null;
    assume true;
    assert {:id "id241"} e#0 != null;
    assert {:id "id242"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id243"} $Unbox(read($Heap, e#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 2;
    assert {:id "id244"} e#0 != null;
    assume true;
    assert {:id "id245"} e#0 != null;
    assert {:id "id246"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id247"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
    assert {:id "id248"} e#0 != null;
    assume true;
    assert {:id "id249"} e#0 != null;
    assert {:id "id250"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id251"} $Unbox(read($Heap, e#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
    assert {:id "id252"} f#0 != null;
    assume true;
    assert {:id "id253"} f#0 != null;
    assert {:id "id254"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id255"} $Unbox(read($Heap, f#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 2;
    assert {:id "id256"} f#0 != null;
    assume true;
    assert {:id "id257"} f#0 != null;
    assert {:id "id258"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id259"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
    assert {:id "id260"} f#0 != null;
    assume true;
    assert {:id "id261"} f#0 != null;
    assert {:id "id262"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id263"} $Unbox(read($Heap, f#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
}



procedure {:verboseName "DoubleBump (call)"} Call$$_module.__default.DoubleBump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]));
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id264"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id265"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id266"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id267"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id268"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id269"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id270"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id271"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id272"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id273"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id274"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id275"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id276"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id277"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id278"} e#0 != f#0;
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
  ensures {:id "id279"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id280"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id281"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id282"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id283"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id284"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id285"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id286"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id287"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id288"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id289"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id290"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id291"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id292"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id293"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id294"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id295"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id296"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;



procedure {:verboseName "DoubleBump (correctness)"} Impl$$_module.__default.DoubleBump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]))
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id297"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id298"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id299"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id300"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id301"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id302"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id303"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id304"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id305"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id306"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id307"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id308"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id309"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id310"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id311"} e#0 != f#0;
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
  ensures {:id "id312"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id313"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id314"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id315"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id316"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id317"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id318"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id319"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id320"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id321"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id322"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id323"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id324"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id325"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id326"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id327"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id328"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id329"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;



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
    assume {:captureState "Test/arith.dfy(44,0): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(45,7)
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
    assert {:id "id330"} a##0 == a#0
       || a##0 == b#0
       || a##0 == c#0
       || a##0 == d#0
       || a##0 == e#0
       || a##0 == f#0
       || !old($Alloc)[a##0];
    assert {:id "id331"} b##0 == a#0
       || b##0 == b#0
       || b##0 == c#0
       || b##0 == d#0
       || b##0 == e#0
       || b##0 == f#0
       || !old($Alloc)[b##0];
    assert {:id "id332"} c##0 == a#0
       || c##0 == b#0
       || c##0 == c#0
       || c##0 == d#0
       || c##0 == e#0
       || c##0 == f#0
       || !old($Alloc)[c##0];
    assert {:id "id333"} d##0 == a#0
       || d##0 == b#0
       || d##0 == c#0
       || d##0 == d#0
       || d##0 == e#0
       || d##0 == f#0
       || !old($Alloc)[d##0];
    assert {:id "id334"} e##0 == a#0
       || e##0 == b#0
       || e##0 == c#0
       || e##0 == d#0
       || e##0 == e#0
       || e##0 == f#0
       || !old($Alloc)[e##0];
    assert {:id "id335"} f##0 == a#0
       || f##0 == b#0
       || f##0 == c#0
       || f##0 == d#0
       || f##0 == e#0
       || f##0 == f#0
       || !old($Alloc)[f##0];
    call {:id "id336"} Call$$_module.__default.Bump(a##0, b##0, c##0, d##0, e##0, f##0);
    // qf-call-frame Bump: supports=12 reads=36 modified=6
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
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(45,24)"} true;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(46,7)
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
    assert {:id "id337"} a##1 == a#0
       || a##1 == b#0
       || a##1 == c#0
       || a##1 == d#0
       || a##1 == e#0
       || a##1 == f#0
       || !old($Alloc)[a##1];
    assert {:id "id338"} b##1 == a#0
       || b##1 == b#0
       || b##1 == c#0
       || b##1 == d#0
       || b##1 == e#0
       || b##1 == f#0
       || !old($Alloc)[b##1];
    assert {:id "id339"} c##1 == a#0
       || c##1 == b#0
       || c##1 == c#0
       || c##1 == d#0
       || c##1 == e#0
       || c##1 == f#0
       || !old($Alloc)[c##1];
    assert {:id "id340"} d##1 == a#0
       || d##1 == b#0
       || d##1 == c#0
       || d##1 == d#0
       || d##1 == e#0
       || d##1 == f#0
       || !old($Alloc)[d##1];
    assert {:id "id341"} e##1 == a#0
       || e##1 == b#0
       || e##1 == c#0
       || e##1 == d#0
       || e##1 == e#0
       || e##1 == f#0
       || !old($Alloc)[e##1];
    assert {:id "id342"} f##1 == a#0
       || f##1 == b#0
       || f##1 == c#0
       || f##1 == d#0
       || f##1 == e#0
       || f##1 == f#0
       || !old($Alloc)[f##1];
    call {:id "id343"} Call$$_module.__default.Bump(a##1, b##1, c##1, d##1, e##1, f##1);
    // qf-call-frame Bump: supports=18 reads=54 modified=6
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
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(46,24)"} true;
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
    assume {:captureState "Test/arith.dfy(49,7): initial state"} true;
    assume {:id "id344"} a#0 != b#0;
    assume {:id "id345"} a#0 != c#0;
    assume {:id "id346"} a#0 != d#0;
    assume {:id "id347"} a#0 != e#0;
    assume {:id "id348"} a#0 != f#0;
    assume {:id "id349"} b#0 != c#0;
    assume {:id "id350"} b#0 != d#0;
    assume {:id "id351"} b#0 != e#0;
    assume {:id "id352"} b#0 != f#0;
    assume {:id "id353"} c#0 != d#0;
    assume {:id "id354"} c#0 != e#0;
    assume {:id "id355"} c#0 != f#0;
    assume {:id "id356"} d#0 != e#0;
    assume {:id "id357"} d#0 != f#0;
    assume {:id "id358"} e#0 != f#0;
    havoc $Heap;
    assume {:captureState "Test/arith.dfy(55,57): post-state"} true;
    assert {:id "id359"} a#0 != null;
    assume true;
    assert {:id "id360"} a#0 != null;
    assert {:id "id361"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id362"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 4;
    assert {:id "id363"} a#0 != null;
    assume true;
    assert {:id "id364"} a#0 != null;
    assert {:id "id365"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id366"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id367"} a#0 != null;
    assume true;
    assert {:id "id368"} a#0 != null;
    assert {:id "id369"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id370"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id371"} b#0 != null;
    assume true;
    assert {:id "id372"} b#0 != null;
    assert {:id "id373"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id374"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 4;
    assert {:id "id375"} b#0 != null;
    assume true;
    assert {:id "id376"} b#0 != null;
    assert {:id "id377"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id378"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id379"} b#0 != null;
    assume true;
    assert {:id "id380"} b#0 != null;
    assert {:id "id381"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id382"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id383"} c#0 != null;
    assume true;
    assert {:id "id384"} c#0 != null;
    assert {:id "id385"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id386"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 4;
    assert {:id "id387"} c#0 != null;
    assume true;
    assert {:id "id388"} c#0 != null;
    assert {:id "id389"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id390"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id391"} c#0 != null;
    assume true;
    assert {:id "id392"} c#0 != null;
    assert {:id "id393"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id394"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id395"} d#0 != null;
    assume true;
    assert {:id "id396"} d#0 != null;
    assert {:id "id397"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id398"} $Unbox(read($Heap, d#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 4;
    assert {:id "id399"} d#0 != null;
    assume true;
    assert {:id "id400"} d#0 != null;
    assert {:id "id401"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id402"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
    assert {:id "id403"} d#0 != null;
    assume true;
    assert {:id "id404"} d#0 != null;
    assert {:id "id405"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id406"} $Unbox(read($Heap, d#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
    assert {:id "id407"} e#0 != null;
    assume true;
    assert {:id "id408"} e#0 != null;
    assert {:id "id409"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id410"} $Unbox(read($Heap, e#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 4;
    assert {:id "id411"} e#0 != null;
    assume true;
    assert {:id "id412"} e#0 != null;
    assert {:id "id413"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id414"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
    assert {:id "id415"} e#0 != null;
    assume true;
    assert {:id "id416"} e#0 != null;
    assert {:id "id417"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id418"} $Unbox(read($Heap, e#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
    assert {:id "id419"} f#0 != null;
    assume true;
    assert {:id "id420"} f#0 != null;
    assert {:id "id421"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id422"} $Unbox(read($Heap, f#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 4;
    assert {:id "id423"} f#0 != null;
    assume true;
    assert {:id "id424"} f#0 != null;
    assert {:id "id425"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id426"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
    assert {:id "id427"} f#0 != null;
    assume true;
    assert {:id "id428"} f#0 != null;
    assert {:id "id429"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id430"} $Unbox(read($Heap, f#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
}



procedure {:verboseName "QuadBump (call)"} Call$$_module.__default.QuadBump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]));
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id431"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id432"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id433"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id434"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id435"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id436"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id437"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id438"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id439"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id440"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id441"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id442"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id443"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id444"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id445"} e#0 != f#0;
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
  ensures {:id "id446"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id447"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id448"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id449"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id450"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id451"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id452"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id453"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id454"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id455"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id456"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id457"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id458"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id459"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id460"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id461"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id462"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id463"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;



procedure {:verboseName "QuadBump (correctness)"} Impl$$_module.__default.QuadBump(a#0: ref where $Is(a#0, Tclass._module.Node()) && (a#0 == null || $Alloc[a#0]), 
    b#0: ref where $Is(b#0, Tclass._module.Node()) && (b#0 == null || $Alloc[b#0]), 
    c#0: ref where $Is(c#0, Tclass._module.Node()) && (c#0 == null || $Alloc[c#0]), 
    d#0: ref where $Is(d#0, Tclass._module.Node()) && (d#0 == null || $Alloc[d#0]), 
    e#0: ref where $Is(e#0, Tclass._module.Node()) && (e#0 == null || $Alloc[e#0]), 
    f#0: ref where $Is(f#0, Tclass._module.Node()) && (f#0 == null || $Alloc[f#0]))
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id464"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id465"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id466"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id467"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id468"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id469"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id470"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id471"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id472"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id473"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id474"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id475"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id476"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id477"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id478"} e#0 != f#0;
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
  ensures {:id "id479"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id480"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id481"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id482"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id483"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id484"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id485"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id486"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id487"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id488"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id489"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id490"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id491"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id492"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id493"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id494"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + 4;
  free ensures {:always_assume} true;
  ensures {:id "id495"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id496"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;



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
    assume {:captureState "Test/arith.dfy(61,0): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(62,13)
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
    assert {:id "id497"} a##0 == a#0
       || a##0 == b#0
       || a##0 == c#0
       || a##0 == d#0
       || a##0 == e#0
       || a##0 == f#0
       || !old($Alloc)[a##0];
    assert {:id "id498"} b##0 == a#0
       || b##0 == b#0
       || b##0 == c#0
       || b##0 == d#0
       || b##0 == e#0
       || b##0 == f#0
       || !old($Alloc)[b##0];
    assert {:id "id499"} c##0 == a#0
       || c##0 == b#0
       || c##0 == c#0
       || c##0 == d#0
       || c##0 == e#0
       || c##0 == f#0
       || !old($Alloc)[c##0];
    assert {:id "id500"} d##0 == a#0
       || d##0 == b#0
       || d##0 == c#0
       || d##0 == d#0
       || d##0 == e#0
       || d##0 == f#0
       || !old($Alloc)[d##0];
    assert {:id "id501"} e##0 == a#0
       || e##0 == b#0
       || e##0 == c#0
       || e##0 == d#0
       || e##0 == e#0
       || e##0 == f#0
       || !old($Alloc)[e##0];
    assert {:id "id502"} f##0 == a#0
       || f##0 == b#0
       || f##0 == c#0
       || f##0 == d#0
       || f##0 == e#0
       || f##0 == f#0
       || !old($Alloc)[f##0];
    call {:id "id503"} Call$$_module.__default.DoubleBump(a##0, b##0, c##0, d##0, e##0, f##0);
    // qf-call-frame DoubleBump: supports=12 reads=36 modified=6
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
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(62,30)"} true;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(63,13)
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
    assert {:id "id504"} a##1 == a#0
       || a##1 == b#0
       || a##1 == c#0
       || a##1 == d#0
       || a##1 == e#0
       || a##1 == f#0
       || !old($Alloc)[a##1];
    assert {:id "id505"} b##1 == a#0
       || b##1 == b#0
       || b##1 == c#0
       || b##1 == d#0
       || b##1 == e#0
       || b##1 == f#0
       || !old($Alloc)[b##1];
    assert {:id "id506"} c##1 == a#0
       || c##1 == b#0
       || c##1 == c#0
       || c##1 == d#0
       || c##1 == e#0
       || c##1 == f#0
       || !old($Alloc)[c##1];
    assert {:id "id507"} d##1 == a#0
       || d##1 == b#0
       || d##1 == c#0
       || d##1 == d#0
       || d##1 == e#0
       || d##1 == f#0
       || !old($Alloc)[d##1];
    assert {:id "id508"} e##1 == a#0
       || e##1 == b#0
       || e##1 == c#0
       || e##1 == d#0
       || e##1 == e#0
       || e##1 == f#0
       || !old($Alloc)[e##1];
    assert {:id "id509"} f##1 == a#0
       || f##1 == b#0
       || f##1 == c#0
       || f##1 == d#0
       || f##1 == e#0
       || f##1 == f#0
       || !old($Alloc)[f##1];
    call {:id "id510"} Call$$_module.__default.DoubleBump(a##1, b##1, c##1, d##1, e##1, f##1);
    // qf-call-frame DoubleBump: supports=18 reads=54 modified=6
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
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(63,30)"} true;
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
    assume {:captureState "Test/arith.dfy(66,7): initial state"} true;
    assume {:id "id511"} n#0 >= LitInt(0);
    assume {:id "id512"} a#0 != b#0;
    assume {:id "id513"} a#0 != c#0;
    assume {:id "id514"} a#0 != d#0;
    assume {:id "id515"} a#0 != e#0;
    assume {:id "id516"} a#0 != f#0;
    assume {:id "id517"} b#0 != c#0;
    assume {:id "id518"} b#0 != d#0;
    assume {:id "id519"} b#0 != e#0;
    assume {:id "id520"} b#0 != f#0;
    assume {:id "id521"} c#0 != d#0;
    assume {:id "id522"} c#0 != e#0;
    assume {:id "id523"} c#0 != f#0;
    assume {:id "id524"} d#0 != e#0;
    assume {:id "id525"} d#0 != f#0;
    assume {:id "id526"} e#0 != f#0;
    havoc $Heap;
    assume {:captureState "Test/arith.dfy(73,57): post-state"} true;
    assert {:id "id527"} a#0 != null;
    assume true;
    assert {:id "id528"} a#0 != null;
    assert {:id "id529"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id530"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + n#0;
    assert {:id "id531"} a#0 != null;
    assume true;
    assert {:id "id532"} a#0 != null;
    assert {:id "id533"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id534"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id535"} a#0 != null;
    assume true;
    assert {:id "id536"} a#0 != null;
    assert {:id "id537"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id538"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id539"} b#0 != null;
    assume true;
    assert {:id "id540"} b#0 != null;
    assert {:id "id541"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id542"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + n#0;
    assert {:id "id543"} b#0 != null;
    assume true;
    assert {:id "id544"} b#0 != null;
    assert {:id "id545"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id546"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id547"} b#0 != null;
    assume true;
    assert {:id "id548"} b#0 != null;
    assert {:id "id549"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id550"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id551"} c#0 != null;
    assume true;
    assert {:id "id552"} c#0 != null;
    assert {:id "id553"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id554"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + n#0;
    assert {:id "id555"} c#0 != null;
    assume true;
    assert {:id "id556"} c#0 != null;
    assert {:id "id557"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id558"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id559"} c#0 != null;
    assume true;
    assert {:id "id560"} c#0 != null;
    assert {:id "id561"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id562"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id563"} d#0 != null;
    assume true;
    assert {:id "id564"} d#0 != null;
    assert {:id "id565"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id566"} $Unbox(read($Heap, d#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + n#0;
    assert {:id "id567"} d#0 != null;
    assume true;
    assert {:id "id568"} d#0 != null;
    assert {:id "id569"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id570"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
    assert {:id "id571"} d#0 != null;
    assume true;
    assert {:id "id572"} d#0 != null;
    assert {:id "id573"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id574"} $Unbox(read($Heap, d#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
    assert {:id "id575"} e#0 != null;
    assume true;
    assert {:id "id576"} e#0 != null;
    assert {:id "id577"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id578"} $Unbox(read($Heap, e#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + n#0;
    assert {:id "id579"} e#0 != null;
    assume true;
    assert {:id "id580"} e#0 != null;
    assert {:id "id581"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id582"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
    assert {:id "id583"} e#0 != null;
    assume true;
    assert {:id "id584"} e#0 != null;
    assert {:id "id585"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id586"} $Unbox(read($Heap, e#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
    assert {:id "id587"} f#0 != null;
    assume true;
    assert {:id "id588"} f#0 != null;
    assert {:id "id589"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id590"} $Unbox(read($Heap, f#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + n#0;
    assert {:id "id591"} f#0 != null;
    assume true;
    assert {:id "id592"} f#0 != null;
    assert {:id "id593"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id594"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
    assert {:id "id595"} f#0 != null;
    assume true;
    assert {:id "id596"} f#0 != null;
    assert {:id "id597"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id598"} $Unbox(read($Heap, f#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
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
  requires {:id "id599"} n#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id600"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id601"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id602"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id603"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id604"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id605"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id606"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id607"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id608"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id609"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id610"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id611"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id612"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id613"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id614"} e#0 != f#0;
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
  ensures {:id "id615"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + n#0;
  free ensures {:always_assume} true;
  ensures {:id "id616"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id617"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id618"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + n#0;
  free ensures {:always_assume} true;
  ensures {:id "id619"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id620"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id621"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + n#0;
  free ensures {:always_assume} true;
  ensures {:id "id622"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id623"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id624"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + n#0;
  free ensures {:always_assume} true;
  ensures {:id "id625"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id626"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id627"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + n#0;
  free ensures {:always_assume} true;
  ensures {:id "id628"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id629"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id630"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + n#0;
  free ensures {:always_assume} true;
  ensures {:id "id631"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id632"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;



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
  requires {:id "id633"} n#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id634"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id635"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id636"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id637"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id638"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id639"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id640"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id641"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id642"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id643"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id644"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id645"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id646"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id647"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id648"} e#0 != f#0;
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
  ensures {:id "id649"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + n#0;
  free ensures {:always_assume} true;
  ensures {:id "id650"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id651"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id652"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + n#0;
  free ensures {:always_assume} true;
  ensures {:id "id653"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id654"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id655"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + n#0;
  free ensures {:always_assume} true;
  ensures {:id "id656"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id657"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id658"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + n#0;
  free ensures {:always_assume} true;
  ensures {:id "id659"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id660"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id661"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + n#0;
  free ensures {:always_assume} true;
  ensures {:id "id662"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id663"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id664"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + n#0;
  free ensures {:always_assume} true;
  ensures {:id "id665"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id666"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;



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
    assume {:captureState "Test/arith.dfy(79,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(80,9)
    assume true;
    assume true;
    i#0 := LitInt(0);
    assume {:captureState "Test/arith.dfy(80,12)"} true;
    // ----- while statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(81,3)
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
      invariant {:id "id669"} $w$loop#0 ==> LitInt(0) <= i#0;
      invariant {:id "id670"} $w$loop#0 ==> i#0 <= n#0;
      free invariant true;
      invariant {:id "id681"} $w$loop#0
         ==> $Unbox(read($Heap, a#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + i#0;
      invariant {:id "id682"} $w$loop#0
         ==> $Unbox(read($Heap, a#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
      invariant {:id "id683"} $w$loop#0
         ==> $Unbox(read($Heap, a#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
      free invariant true;
      invariant {:id "id694"} $w$loop#0
         ==> $Unbox(read($Heap, b#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + i#0;
      invariant {:id "id695"} $w$loop#0
         ==> $Unbox(read($Heap, b#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
      invariant {:id "id696"} $w$loop#0
         ==> $Unbox(read($Heap, b#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
      free invariant true;
      invariant {:id "id707"} $w$loop#0
         ==> $Unbox(read($Heap, c#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + i#0;
      invariant {:id "id708"} $w$loop#0
         ==> $Unbox(read($Heap, c#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
      invariant {:id "id709"} $w$loop#0
         ==> $Unbox(read($Heap, c#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
      free invariant true;
      invariant {:id "id720"} $w$loop#0
         ==> $Unbox(read($Heap, d#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + i#0;
      invariant {:id "id721"} $w$loop#0
         ==> $Unbox(read($Heap, d#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
      invariant {:id "id722"} $w$loop#0
         ==> $Unbox(read($Heap, d#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
      free invariant true;
      invariant {:id "id733"} $w$loop#0
         ==> $Unbox(read($Heap, e#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + i#0;
      invariant {:id "id734"} $w$loop#0
         ==> $Unbox(read($Heap, e#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
      invariant {:id "id735"} $w$loop#0
         ==> $Unbox(read($Heap, e#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
      free invariant true;
      invariant {:id "id746"} $w$loop#0
         ==> $Unbox(read($Heap, f#0, _module.Node.val)): int
           == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + i#0;
      invariant {:id "id747"} $w$loop#0
         ==> $Unbox(read($Heap, f#0, _module.Node.tag)): int
           == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
      invariant {:id "id748"} $w$loop#0
         ==> $Unbox(read($Heap, f#0, _module.Node.score)): int
           == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
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
      free invariant n#0 - i#0 <= $decr_init$loop#00;
    {
        assume {:captureState "Test/arith.dfy(81,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (LitInt(0) <= i#0)
            {
            }

            assume true;
            assume {:id "id668"} LitInt(0) <= i#0 && i#0 <= n#0;
            assert {:id "id671"} {:subsumption 0} a#0 != null;
            assume true;
            assert {:id "id672"} {:subsumption 0} a#0 != null;
            assert {:id "id673"} a#0 == null || old($Alloc)[a#0];
            assume true;
            if ($Unbox(read($Heap, a#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + i#0)
            {
                assert {:id "id674"} {:subsumption 0} a#0 != null;
                assume true;
                assert {:id "id675"} {:subsumption 0} a#0 != null;
                assert {:id "id676"} a#0 == null || old($Alloc)[a#0];
                assume true;
            }

            if ($Unbox(read($Heap, a#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + i#0
               && $Unbox(read($Heap, a#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int)
            {
                assert {:id "id677"} {:subsumption 0} a#0 != null;
                assume true;
                assert {:id "id678"} {:subsumption 0} a#0 != null;
                assert {:id "id679"} a#0 == null || old($Alloc)[a#0];
                assume true;
            }

            assume true;
            assume {:id "id680"} $Unbox(read($Heap, a#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + i#0
               && $Unbox(read($Heap, a#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int
               && $Unbox(read($Heap, a#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
            assert {:id "id684"} {:subsumption 0} b#0 != null;
            assume true;
            assert {:id "id685"} {:subsumption 0} b#0 != null;
            assert {:id "id686"} b#0 == null || old($Alloc)[b#0];
            assume true;
            if ($Unbox(read($Heap, b#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + i#0)
            {
                assert {:id "id687"} {:subsumption 0} b#0 != null;
                assume true;
                assert {:id "id688"} {:subsumption 0} b#0 != null;
                assert {:id "id689"} b#0 == null || old($Alloc)[b#0];
                assume true;
            }

            if ($Unbox(read($Heap, b#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + i#0
               && $Unbox(read($Heap, b#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int)
            {
                assert {:id "id690"} {:subsumption 0} b#0 != null;
                assume true;
                assert {:id "id691"} {:subsumption 0} b#0 != null;
                assert {:id "id692"} b#0 == null || old($Alloc)[b#0];
                assume true;
            }

            assume true;
            assume {:id "id693"} $Unbox(read($Heap, b#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + i#0
               && $Unbox(read($Heap, b#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int
               && $Unbox(read($Heap, b#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
            assert {:id "id697"} {:subsumption 0} c#0 != null;
            assume true;
            assert {:id "id698"} {:subsumption 0} c#0 != null;
            assert {:id "id699"} c#0 == null || old($Alloc)[c#0];
            assume true;
            if ($Unbox(read($Heap, c#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + i#0)
            {
                assert {:id "id700"} {:subsumption 0} c#0 != null;
                assume true;
                assert {:id "id701"} {:subsumption 0} c#0 != null;
                assert {:id "id702"} c#0 == null || old($Alloc)[c#0];
                assume true;
            }

            if ($Unbox(read($Heap, c#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + i#0
               && $Unbox(read($Heap, c#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int)
            {
                assert {:id "id703"} {:subsumption 0} c#0 != null;
                assume true;
                assert {:id "id704"} {:subsumption 0} c#0 != null;
                assert {:id "id705"} c#0 == null || old($Alloc)[c#0];
                assume true;
            }

            assume true;
            assume {:id "id706"} $Unbox(read($Heap, c#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + i#0
               && $Unbox(read($Heap, c#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int
               && $Unbox(read($Heap, c#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
            assert {:id "id710"} {:subsumption 0} d#0 != null;
            assume true;
            assert {:id "id711"} {:subsumption 0} d#0 != null;
            assert {:id "id712"} d#0 == null || old($Alloc)[d#0];
            assume true;
            if ($Unbox(read($Heap, d#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + i#0)
            {
                assert {:id "id713"} {:subsumption 0} d#0 != null;
                assume true;
                assert {:id "id714"} {:subsumption 0} d#0 != null;
                assert {:id "id715"} d#0 == null || old($Alloc)[d#0];
                assume true;
            }

            if ($Unbox(read($Heap, d#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + i#0
               && $Unbox(read($Heap, d#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int)
            {
                assert {:id "id716"} {:subsumption 0} d#0 != null;
                assume true;
                assert {:id "id717"} {:subsumption 0} d#0 != null;
                assert {:id "id718"} d#0 == null || old($Alloc)[d#0];
                assume true;
            }

            assume true;
            assume {:id "id719"} $Unbox(read($Heap, d#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + i#0
               && $Unbox(read($Heap, d#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int
               && $Unbox(read($Heap, d#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
            assert {:id "id723"} {:subsumption 0} e#0 != null;
            assume true;
            assert {:id "id724"} {:subsumption 0} e#0 != null;
            assert {:id "id725"} e#0 == null || old($Alloc)[e#0];
            assume true;
            if ($Unbox(read($Heap, e#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + i#0)
            {
                assert {:id "id726"} {:subsumption 0} e#0 != null;
                assume true;
                assert {:id "id727"} {:subsumption 0} e#0 != null;
                assert {:id "id728"} e#0 == null || old($Alloc)[e#0];
                assume true;
            }

            if ($Unbox(read($Heap, e#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + i#0
               && $Unbox(read($Heap, e#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int)
            {
                assert {:id "id729"} {:subsumption 0} e#0 != null;
                assume true;
                assert {:id "id730"} {:subsumption 0} e#0 != null;
                assert {:id "id731"} e#0 == null || old($Alloc)[e#0];
                assume true;
            }

            assume true;
            assume {:id "id732"} $Unbox(read($Heap, e#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + i#0
               && $Unbox(read($Heap, e#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int
               && $Unbox(read($Heap, e#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
            assert {:id "id736"} {:subsumption 0} f#0 != null;
            assume true;
            assert {:id "id737"} {:subsumption 0} f#0 != null;
            assert {:id "id738"} f#0 == null || old($Alloc)[f#0];
            assume true;
            if ($Unbox(read($Heap, f#0, _module.Node.val)): int
               == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + i#0)
            {
                assert {:id "id739"} {:subsumption 0} f#0 != null;
                assume true;
                assert {:id "id740"} {:subsumption 0} f#0 != null;
                assert {:id "id741"} f#0 == null || old($Alloc)[f#0];
                assume true;
            }

            if ($Unbox(read($Heap, f#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + i#0
               && $Unbox(read($Heap, f#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int)
            {
                assert {:id "id742"} {:subsumption 0} f#0 != null;
                assume true;
                assert {:id "id743"} {:subsumption 0} f#0 != null;
                assert {:id "id744"} f#0 == null || old($Alloc)[f#0];
                assume true;
            }

            assume true;
            assume {:id "id745"} $Unbox(read($Heap, f#0, _module.Node.val)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + i#0
               && $Unbox(read($Heap, f#0, _module.Node.tag)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int
               && $Unbox(read($Heap, f#0, _module.Node.score)): int
                 == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
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
        // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(90,9)
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
        assert {:id "id749"} a##0_0 == a#0
           || a##0_0 == b#0
           || a##0_0 == c#0
           || a##0_0 == d#0
           || a##0_0 == e#0
           || a##0_0 == f#0
           || !old($Alloc)[a##0_0];
        assert {:id "id750"} b##0_0 == a#0
           || b##0_0 == b#0
           || b##0_0 == c#0
           || b##0_0 == d#0
           || b##0_0 == e#0
           || b##0_0 == f#0
           || !old($Alloc)[b##0_0];
        assert {:id "id751"} c##0_0 == a#0
           || c##0_0 == b#0
           || c##0_0 == c#0
           || c##0_0 == d#0
           || c##0_0 == e#0
           || c##0_0 == f#0
           || !old($Alloc)[c##0_0];
        assert {:id "id752"} d##0_0 == a#0
           || d##0_0 == b#0
           || d##0_0 == c#0
           || d##0_0 == d#0
           || d##0_0 == e#0
           || d##0_0 == f#0
           || !old($Alloc)[d##0_0];
        assert {:id "id753"} e##0_0 == a#0
           || e##0_0 == b#0
           || e##0_0 == c#0
           || e##0_0 == d#0
           || e##0_0 == e#0
           || e##0_0 == f#0
           || !old($Alloc)[e##0_0];
        assert {:id "id754"} f##0_0 == a#0
           || f##0_0 == b#0
           || f##0_0 == c#0
           || f##0_0 == d#0
           || f##0_0 == e#0
           || f##0_0 == f#0
           || !old($Alloc)[f##0_0];
        call {:id "id755"} Call$$_module.__default.Bump(a##0_0, b##0_0, c##0_0, d##0_0, e##0_0, f##0_0);
        // qf-call-frame Bump: supports=12 reads=36 modified=6
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
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "Test/arith.dfy(90,26)"} true;
        // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(91,7)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "Test/arith.dfy(91,14)"} true;
        assume true;
        // ----- loop termination check ----- /Users/saline/development/projects/dafny/Test/arith.dfy(81,3)
        assert {:id "id757"} 0 <= $decr$loop#00 || n#0 - i#0 == $decr$loop#00;
        assert {:id "id758"} n#0 - i#0 < $decr$loop#00;
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
    n#0: int)
{

    // AddMethodImpl: StressTest, CheckWellFormed$$_module.__default.StressTest
    assume {:captureState "Test/arith.dfy(95,7): initial state"} true;
    assume {:id "id759"} n#0 >= LitInt(0);
    assume {:id "id760"} a#0 != b#0;
    assume {:id "id761"} a#0 != c#0;
    assume {:id "id762"} a#0 != d#0;
    assume {:id "id763"} a#0 != e#0;
    assume {:id "id764"} a#0 != f#0;
    assume {:id "id765"} b#0 != c#0;
    assume {:id "id766"} b#0 != d#0;
    assume {:id "id767"} b#0 != e#0;
    assume {:id "id768"} b#0 != f#0;
    assume {:id "id769"} c#0 != d#0;
    assume {:id "id770"} c#0 != e#0;
    assume {:id "id771"} c#0 != f#0;
    assume {:id "id772"} d#0 != e#0;
    assume {:id "id773"} d#0 != f#0;
    assume {:id "id774"} e#0 != f#0;
    assume {:id "id775"} p#0 != q#0;
    assume {:id "id776"} p#0 != r#0;
    assume {:id "id777"} p#0 != s#0;
    assume {:id "id778"} p#0 != t#0;
    assume {:id "id779"} p#0 != u#0;
    assume {:id "id780"} q#0 != r#0;
    assume {:id "id781"} q#0 != s#0;
    assume {:id "id782"} q#0 != t#0;
    assume {:id "id783"} q#0 != u#0;
    assume {:id "id784"} r#0 != s#0;
    assume {:id "id785"} r#0 != t#0;
    assume {:id "id786"} r#0 != u#0;
    assume {:id "id787"} s#0 != t#0;
    assume {:id "id788"} s#0 != u#0;
    assume {:id "id789"} t#0 != u#0;
    assume {:id "id790"} a#0 != p#0;
    assume {:id "id791"} a#0 != q#0;
    assume {:id "id792"} a#0 != r#0;
    assume {:id "id793"} a#0 != s#0;
    assume {:id "id794"} a#0 != t#0;
    assume {:id "id795"} a#0 != u#0;
    assume {:id "id796"} b#0 != p#0;
    assume {:id "id797"} b#0 != q#0;
    assume {:id "id798"} b#0 != r#0;
    assume {:id "id799"} b#0 != s#0;
    assume {:id "id800"} b#0 != t#0;
    assume {:id "id801"} b#0 != u#0;
    assume {:id "id802"} c#0 != p#0;
    assume {:id "id803"} c#0 != q#0;
    assume {:id "id804"} c#0 != r#0;
    assume {:id "id805"} c#0 != s#0;
    assume {:id "id806"} c#0 != t#0;
    assume {:id "id807"} c#0 != u#0;
    assume {:id "id808"} d#0 != p#0;
    assume {:id "id809"} d#0 != q#0;
    assume {:id "id810"} d#0 != r#0;
    assume {:id "id811"} d#0 != s#0;
    assume {:id "id812"} d#0 != t#0;
    assume {:id "id813"} d#0 != u#0;
    assume {:id "id814"} e#0 != p#0;
    assume {:id "id815"} e#0 != q#0;
    assume {:id "id816"} e#0 != r#0;
    assume {:id "id817"} e#0 != s#0;
    assume {:id "id818"} e#0 != t#0;
    assume {:id "id819"} e#0 != u#0;
    assume {:id "id820"} f#0 != p#0;
    assume {:id "id821"} f#0 != q#0;
    assume {:id "id822"} f#0 != r#0;
    assume {:id "id823"} f#0 != s#0;
    assume {:id "id824"} f#0 != t#0;
    assume {:id "id825"} f#0 != u#0;
    havoc $Heap;
    assume {:captureState "Test/arith.dfy(118,61): post-state"} true;
    assert {:id "id826"} a#0 != null;
    assume true;
    assert {:id "id827"} a#0 != null;
    assert {:id "id828"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id829"} $Unbox(read($Heap, a#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + n#0 + 4;
    assert {:id "id830"} a#0 != null;
    assume true;
    assert {:id "id831"} a#0 != null;
    assert {:id "id832"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id833"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
    assert {:id "id834"} a#0 != null;
    assume true;
    assert {:id "id835"} a#0 != null;
    assert {:id "id836"} a#0 == null || old($Alloc)[a#0];
    assume true;
    assume {:id "id837"} $Unbox(read($Heap, a#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
    assert {:id "id838"} b#0 != null;
    assume true;
    assert {:id "id839"} b#0 != null;
    assert {:id "id840"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id841"} $Unbox(read($Heap, b#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + n#0 + 4;
    assert {:id "id842"} b#0 != null;
    assume true;
    assert {:id "id843"} b#0 != null;
    assert {:id "id844"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id845"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
    assert {:id "id846"} b#0 != null;
    assume true;
    assert {:id "id847"} b#0 != null;
    assert {:id "id848"} b#0 == null || old($Alloc)[b#0];
    assume true;
    assume {:id "id849"} $Unbox(read($Heap, b#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
    assert {:id "id850"} c#0 != null;
    assume true;
    assert {:id "id851"} c#0 != null;
    assert {:id "id852"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id853"} $Unbox(read($Heap, c#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + n#0 + 4;
    assert {:id "id854"} c#0 != null;
    assume true;
    assert {:id "id855"} c#0 != null;
    assert {:id "id856"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id857"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
    assert {:id "id858"} c#0 != null;
    assume true;
    assert {:id "id859"} c#0 != null;
    assert {:id "id860"} c#0 == null || old($Alloc)[c#0];
    assume true;
    assume {:id "id861"} $Unbox(read($Heap, c#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
    assert {:id "id862"} d#0 != null;
    assume true;
    assert {:id "id863"} d#0 != null;
    assert {:id "id864"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id865"} $Unbox(read($Heap, d#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + n#0 + 4;
    assert {:id "id866"} d#0 != null;
    assume true;
    assert {:id "id867"} d#0 != null;
    assert {:id "id868"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id869"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
    assert {:id "id870"} d#0 != null;
    assume true;
    assert {:id "id871"} d#0 != null;
    assert {:id "id872"} d#0 == null || old($Alloc)[d#0];
    assume true;
    assume {:id "id873"} $Unbox(read($Heap, d#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
    assert {:id "id874"} e#0 != null;
    assume true;
    assert {:id "id875"} e#0 != null;
    assert {:id "id876"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id877"} $Unbox(read($Heap, e#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + n#0 + 4;
    assert {:id "id878"} e#0 != null;
    assume true;
    assert {:id "id879"} e#0 != null;
    assert {:id "id880"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id881"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
    assert {:id "id882"} e#0 != null;
    assume true;
    assert {:id "id883"} e#0 != null;
    assert {:id "id884"} e#0 == null || old($Alloc)[e#0];
    assume true;
    assume {:id "id885"} $Unbox(read($Heap, e#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
    assert {:id "id886"} f#0 != null;
    assume true;
    assert {:id "id887"} f#0 != null;
    assert {:id "id888"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id889"} $Unbox(read($Heap, f#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + n#0 + 4;
    assert {:id "id890"} f#0 != null;
    assume true;
    assert {:id "id891"} f#0 != null;
    assert {:id "id892"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id893"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
    assert {:id "id894"} f#0 != null;
    assume true;
    assert {:id "id895"} f#0 != null;
    assert {:id "id896"} f#0 == null || old($Alloc)[f#0];
    assume true;
    assume {:id "id897"} $Unbox(read($Heap, f#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
    assert {:id "id898"} p#0 != null;
    assume true;
    assert {:id "id899"} p#0 != null;
    assert {:id "id900"} p#0 == null || old($Alloc)[p#0];
    assume true;
    assume {:id "id901"} $Unbox(read($Heap, p#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), p#0, _module.Node.val)): int + 2;
    assert {:id "id902"} p#0 != null;
    assume true;
    assert {:id "id903"} p#0 != null;
    assert {:id "id904"} p#0 == null || old($Alloc)[p#0];
    assume true;
    assume {:id "id905"} $Unbox(read($Heap, p#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), p#0, _module.Node.tag)): int;
    assert {:id "id906"} p#0 != null;
    assume true;
    assert {:id "id907"} p#0 != null;
    assert {:id "id908"} p#0 == null || old($Alloc)[p#0];
    assume true;
    assume {:id "id909"} $Unbox(read($Heap, p#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), p#0, _module.Node.score)): int;
    assert {:id "id910"} q#0 != null;
    assume true;
    assert {:id "id911"} q#0 != null;
    assert {:id "id912"} q#0 == null || old($Alloc)[q#0];
    assume true;
    assume {:id "id913"} $Unbox(read($Heap, q#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), q#0, _module.Node.val)): int + 2;
    assert {:id "id914"} q#0 != null;
    assume true;
    assert {:id "id915"} q#0 != null;
    assert {:id "id916"} q#0 == null || old($Alloc)[q#0];
    assume true;
    assume {:id "id917"} $Unbox(read($Heap, q#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), q#0, _module.Node.tag)): int;
    assert {:id "id918"} q#0 != null;
    assume true;
    assert {:id "id919"} q#0 != null;
    assert {:id "id920"} q#0 == null || old($Alloc)[q#0];
    assume true;
    assume {:id "id921"} $Unbox(read($Heap, q#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), q#0, _module.Node.score)): int;
    assert {:id "id922"} r#0 != null;
    assume true;
    assert {:id "id923"} r#0 != null;
    assert {:id "id924"} r#0 == null || old($Alloc)[r#0];
    assume true;
    assume {:id "id925"} $Unbox(read($Heap, r#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), r#0, _module.Node.val)): int + 2;
    assert {:id "id926"} r#0 != null;
    assume true;
    assert {:id "id927"} r#0 != null;
    assert {:id "id928"} r#0 == null || old($Alloc)[r#0];
    assume true;
    assume {:id "id929"} $Unbox(read($Heap, r#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), r#0, _module.Node.tag)): int;
    assert {:id "id930"} r#0 != null;
    assume true;
    assert {:id "id931"} r#0 != null;
    assert {:id "id932"} r#0 == null || old($Alloc)[r#0];
    assume true;
    assume {:id "id933"} $Unbox(read($Heap, r#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), r#0, _module.Node.score)): int;
    assert {:id "id934"} s#0 != null;
    assume true;
    assert {:id "id935"} s#0 != null;
    assert {:id "id936"} s#0 == null || old($Alloc)[s#0];
    assume true;
    assume {:id "id937"} $Unbox(read($Heap, s#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), s#0, _module.Node.val)): int + 2;
    assert {:id "id938"} s#0 != null;
    assume true;
    assert {:id "id939"} s#0 != null;
    assert {:id "id940"} s#0 == null || old($Alloc)[s#0];
    assume true;
    assume {:id "id941"} $Unbox(read($Heap, s#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), s#0, _module.Node.tag)): int;
    assert {:id "id942"} s#0 != null;
    assume true;
    assert {:id "id943"} s#0 != null;
    assert {:id "id944"} s#0 == null || old($Alloc)[s#0];
    assume true;
    assume {:id "id945"} $Unbox(read($Heap, s#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), s#0, _module.Node.score)): int;
    assert {:id "id946"} t#0 != null;
    assume true;
    assert {:id "id947"} t#0 != null;
    assert {:id "id948"} t#0 == null || old($Alloc)[t#0];
    assume true;
    assume {:id "id949"} $Unbox(read($Heap, t#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), t#0, _module.Node.val)): int + 2;
    assert {:id "id950"} t#0 != null;
    assume true;
    assert {:id "id951"} t#0 != null;
    assert {:id "id952"} t#0 == null || old($Alloc)[t#0];
    assume true;
    assume {:id "id953"} $Unbox(read($Heap, t#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), t#0, _module.Node.tag)): int;
    assert {:id "id954"} t#0 != null;
    assume true;
    assert {:id "id955"} t#0 != null;
    assert {:id "id956"} t#0 == null || old($Alloc)[t#0];
    assume true;
    assume {:id "id957"} $Unbox(read($Heap, t#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), t#0, _module.Node.score)): int;
    assert {:id "id958"} u#0 != null;
    assume true;
    assert {:id "id959"} u#0 != null;
    assert {:id "id960"} u#0 == null || old($Alloc)[u#0];
    assume true;
    assume {:id "id961"} $Unbox(read($Heap, u#0, _module.Node.val)): int
       == $Unbox(read(old($Heap), u#0, _module.Node.val)): int + 2;
    assert {:id "id962"} u#0 != null;
    assume true;
    assert {:id "id963"} u#0 != null;
    assert {:id "id964"} u#0 == null || old($Alloc)[u#0];
    assume true;
    assume {:id "id965"} $Unbox(read($Heap, u#0, _module.Node.tag)): int
       == $Unbox(read(old($Heap), u#0, _module.Node.tag)): int;
    assert {:id "id966"} u#0 != null;
    assume true;
    assert {:id "id967"} u#0 != null;
    assert {:id "id968"} u#0 == null || old($Alloc)[u#0];
    assume true;
    assume {:id "id969"} $Unbox(read($Heap, u#0, _module.Node.score)): int
       == $Unbox(read(old($Heap), u#0, _module.Node.score)): int;
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
    n#0: int);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id970"} n#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id971"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id972"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id973"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id974"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id975"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id976"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id977"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id978"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id979"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id980"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id981"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id982"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id983"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id984"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id985"} e#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id986"} p#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id987"} p#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id988"} p#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id989"} p#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id990"} p#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id991"} q#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id992"} q#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id993"} q#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id994"} q#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id995"} r#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id996"} r#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id997"} r#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id998"} s#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id999"} s#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1000"} t#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1001"} a#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1002"} a#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1003"} a#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1004"} a#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1005"} a#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1006"} a#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1007"} b#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1008"} b#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1009"} b#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1010"} b#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1011"} b#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1012"} b#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1013"} c#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1014"} c#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1015"} c#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1016"} c#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1017"} c#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1018"} c#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1019"} d#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1020"} d#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1021"} d#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1022"} d#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1023"} d#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1024"} d#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1025"} e#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1026"} e#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1027"} e#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1028"} e#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1029"} e#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1030"} e#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1031"} f#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1032"} f#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1033"} f#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1034"} f#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1035"} f#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1036"} f#0 != u#0;
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
  ensures {:id "id1037"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + n#0 + 4;
  free ensures {:always_assume} true;
  ensures {:id "id1038"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1039"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1040"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + n#0 + 4;
  free ensures {:always_assume} true;
  ensures {:id "id1041"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1042"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1043"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + n#0 + 4;
  free ensures {:always_assume} true;
  ensures {:id "id1044"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1045"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1046"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + n#0 + 4;
  free ensures {:always_assume} true;
  ensures {:id "id1047"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1048"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1049"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + n#0 + 4;
  free ensures {:always_assume} true;
  ensures {:id "id1050"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1051"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1052"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + n#0 + 4;
  free ensures {:always_assume} true;
  ensures {:id "id1053"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1054"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1055"} $Unbox(read($Heap, p#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id1056"} $Unbox(read($Heap, p#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1057"} $Unbox(read($Heap, p#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1058"} $Unbox(read($Heap, q#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id1059"} $Unbox(read($Heap, q#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1060"} $Unbox(read($Heap, q#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1061"} $Unbox(read($Heap, r#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id1062"} $Unbox(read($Heap, r#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1063"} $Unbox(read($Heap, r#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1064"} $Unbox(read($Heap, s#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id1065"} $Unbox(read($Heap, s#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1066"} $Unbox(read($Heap, s#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1067"} $Unbox(read($Heap, t#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id1068"} $Unbox(read($Heap, t#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1069"} $Unbox(read($Heap, t#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1070"} $Unbox(read($Heap, u#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id1071"} $Unbox(read($Heap, u#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1072"} $Unbox(read($Heap, u#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.score)): int;



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
    n#0: int)
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id1073"} n#0 >= LitInt(0);
  free requires {:always_assume} true;
  requires {:id "id1074"} a#0 != b#0;
  free requires {:always_assume} true;
  requires {:id "id1075"} a#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1076"} a#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1077"} a#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1078"} a#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1079"} b#0 != c#0;
  free requires {:always_assume} true;
  requires {:id "id1080"} b#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1081"} b#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1082"} b#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1083"} c#0 != d#0;
  free requires {:always_assume} true;
  requires {:id "id1084"} c#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1085"} c#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1086"} d#0 != e#0;
  free requires {:always_assume} true;
  requires {:id "id1087"} d#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1088"} e#0 != f#0;
  free requires {:always_assume} true;
  requires {:id "id1089"} p#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1090"} p#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1091"} p#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1092"} p#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1093"} p#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1094"} q#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1095"} q#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1096"} q#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1097"} q#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1098"} r#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1099"} r#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1100"} r#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1101"} s#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1102"} s#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1103"} t#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1104"} a#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1105"} a#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1106"} a#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1107"} a#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1108"} a#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1109"} a#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1110"} b#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1111"} b#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1112"} b#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1113"} b#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1114"} b#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1115"} b#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1116"} c#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1117"} c#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1118"} c#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1119"} c#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1120"} c#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1121"} c#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1122"} d#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1123"} d#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1124"} d#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1125"} d#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1126"} d#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1127"} d#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1128"} e#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1129"} e#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1130"} e#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1131"} e#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1132"} e#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1133"} e#0 != u#0;
  free requires {:always_assume} true;
  requires {:id "id1134"} f#0 != p#0;
  free requires {:always_assume} true;
  requires {:id "id1135"} f#0 != q#0;
  free requires {:always_assume} true;
  requires {:id "id1136"} f#0 != r#0;
  free requires {:always_assume} true;
  requires {:id "id1137"} f#0 != s#0;
  free requires {:always_assume} true;
  requires {:id "id1138"} f#0 != t#0;
  free requires {:always_assume} true;
  requires {:id "id1139"} f#0 != u#0;
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
  ensures {:id "id1140"} $Unbox(read($Heap, a#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.val)): int + n#0 + 4;
  free ensures {:always_assume} true;
  ensures {:id "id1141"} $Unbox(read($Heap, a#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1142"} $Unbox(read($Heap, a#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), a#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1143"} $Unbox(read($Heap, b#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.val)): int + n#0 + 4;
  free ensures {:always_assume} true;
  ensures {:id "id1144"} $Unbox(read($Heap, b#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1145"} $Unbox(read($Heap, b#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), b#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1146"} $Unbox(read($Heap, c#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.val)): int + n#0 + 4;
  free ensures {:always_assume} true;
  ensures {:id "id1147"} $Unbox(read($Heap, c#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1148"} $Unbox(read($Heap, c#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), c#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1149"} $Unbox(read($Heap, d#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.val)): int + n#0 + 4;
  free ensures {:always_assume} true;
  ensures {:id "id1150"} $Unbox(read($Heap, d#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1151"} $Unbox(read($Heap, d#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), d#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1152"} $Unbox(read($Heap, e#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.val)): int + n#0 + 4;
  free ensures {:always_assume} true;
  ensures {:id "id1153"} $Unbox(read($Heap, e#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1154"} $Unbox(read($Heap, e#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), e#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1155"} $Unbox(read($Heap, f#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.val)): int + n#0 + 4;
  free ensures {:always_assume} true;
  ensures {:id "id1156"} $Unbox(read($Heap, f#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1157"} $Unbox(read($Heap, f#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), f#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1158"} $Unbox(read($Heap, p#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id1159"} $Unbox(read($Heap, p#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1160"} $Unbox(read($Heap, p#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), p#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1161"} $Unbox(read($Heap, q#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id1162"} $Unbox(read($Heap, q#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1163"} $Unbox(read($Heap, q#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), q#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1164"} $Unbox(read($Heap, r#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id1165"} $Unbox(read($Heap, r#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1166"} $Unbox(read($Heap, r#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), r#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1167"} $Unbox(read($Heap, s#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id1168"} $Unbox(read($Heap, s#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1169"} $Unbox(read($Heap, s#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), s#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1170"} $Unbox(read($Heap, t#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id1171"} $Unbox(read($Heap, t#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1172"} $Unbox(read($Heap, t#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), t#0, _module.Node.score)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1173"} $Unbox(read($Heap, u#0, _module.Node.val)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.val)): int + 2;
  free ensures {:always_assume} true;
  ensures {:id "id1174"} $Unbox(read($Heap, u#0, _module.Node.tag)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.tag)): int;
  free ensures {:always_assume} true;
  ensures {:id "id1175"} $Unbox(read($Heap, u#0, _module.Node.score)): int
     == $Unbox(read(old($Heap), u#0, _module.Node.score)): int;



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

    // AddMethodImpl: StressTest, Impl$$_module.__default.StressTest
    assume {:captureState "Test/arith.dfy(130,0): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(131,8)
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
    n##0 := n#0;
    $PreCallHeap#0 := $Heap;
    $PreCallAlloc#0 := $Alloc;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id1176"} a##0 == a#0
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
    assert {:id "id1177"} b##0 == a#0
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
    assert {:id "id1178"} c##0 == a#0
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
    assert {:id "id1179"} d##0 == a#0
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
    assert {:id "id1180"} e##0 == a#0
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
    assert {:id "id1181"} f##0 == a#0
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
    call {:id "id1182"} Call$$_module.__default.BumpN(a##0, b##0, c##0, d##0, e##0, f##0, n##0);
    // qf-call-frame BumpN: supports=18 reads=54 modified=6
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
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(131,28)"} true;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(132,11)
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
    assert {:id "id1183"} a##1 == a#0
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
    assert {:id "id1184"} b##1 == a#0
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
    assert {:id "id1185"} c##1 == a#0
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
    assert {:id "id1186"} d##1 == a#0
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
    assert {:id "id1187"} e##1 == a#0
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
    assert {:id "id1188"} f##1 == a#0
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
    call {:id "id1189"} Call$$_module.__default.QuadBump(a##1, b##1, c##1, d##1, e##1, f##1);
    // qf-call-frame QuadBump: supports=24 reads=72 modified=6
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
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(132,28)"} true;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(133,13)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##2 := p#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##2 := q#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##2 := r#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##2 := s#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    e##2 := t#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    f##2 := u#0;
    $PreCallHeap#2 := $Heap;
    $PreCallAlloc#2 := $Alloc;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    assert {:id "id1190"} a##2 == a#0
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
    assert {:id "id1191"} b##2 == a#0
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
    assert {:id "id1192"} c##2 == a#0
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
    assert {:id "id1193"} d##2 == a#0
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
    assert {:id "id1194"} e##2 == a#0
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
    assert {:id "id1195"} f##2 == a#0
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
    call {:id "id1196"} Call$$_module.__default.DoubleBump(a##2, b##2, c##2, d##2, e##2, f##2);
    // qf-call-frame DoubleBump: supports=30 reads=90 modified=6
    assume p#0 != null
         && p#0 != p#0
         && p#0 != q#0
         && p#0 != r#0
         && p#0 != s#0
         && p#0 != t#0
         && p#0 != u#0
       ==> read($Heap, p#0, _module.Node.val)
         == read($PreCallHeap#2, p#0, _module.Node.val);
    assume p#0 != null
         && p#0 != p#0
         && p#0 != q#0
         && p#0 != r#0
         && p#0 != s#0
         && p#0 != t#0
         && p#0 != u#0
       ==> read($Heap, p#0, _module.Node.tag)
         == read($PreCallHeap#2, p#0, _module.Node.tag);
    assume p#0 != null
         && p#0 != p#0
         && p#0 != q#0
         && p#0 != r#0
         && p#0 != s#0
         && p#0 != t#0
         && p#0 != u#0
       ==> read($Heap, p#0, _module.Node.score)
         == read($PreCallHeap#2, p#0, _module.Node.score);
    assume q#0 != null
         && q#0 != p#0
         && q#0 != q#0
         && q#0 != r#0
         && q#0 != s#0
         && q#0 != t#0
         && q#0 != u#0
       ==> read($Heap, q#0, _module.Node.val)
         == read($PreCallHeap#2, q#0, _module.Node.val);
    assume q#0 != null
         && q#0 != p#0
         && q#0 != q#0
         && q#0 != r#0
         && q#0 != s#0
         && q#0 != t#0
         && q#0 != u#0
       ==> read($Heap, q#0, _module.Node.tag)
         == read($PreCallHeap#2, q#0, _module.Node.tag);
    assume q#0 != null
         && q#0 != p#0
         && q#0 != q#0
         && q#0 != r#0
         && q#0 != s#0
         && q#0 != t#0
         && q#0 != u#0
       ==> read($Heap, q#0, _module.Node.score)
         == read($PreCallHeap#2, q#0, _module.Node.score);
    assume r#0 != null
         && r#0 != p#0
         && r#0 != q#0
         && r#0 != r#0
         && r#0 != s#0
         && r#0 != t#0
         && r#0 != u#0
       ==> read($Heap, r#0, _module.Node.val)
         == read($PreCallHeap#2, r#0, _module.Node.val);
    assume r#0 != null
         && r#0 != p#0
         && r#0 != q#0
         && r#0 != r#0
         && r#0 != s#0
         && r#0 != t#0
         && r#0 != u#0
       ==> read($Heap, r#0, _module.Node.tag)
         == read($PreCallHeap#2, r#0, _module.Node.tag);
    assume r#0 != null
         && r#0 != p#0
         && r#0 != q#0
         && r#0 != r#0
         && r#0 != s#0
         && r#0 != t#0
         && r#0 != u#0
       ==> read($Heap, r#0, _module.Node.score)
         == read($PreCallHeap#2, r#0, _module.Node.score);
    assume s#0 != null
         && s#0 != p#0
         && s#0 != q#0
         && s#0 != r#0
         && s#0 != s#0
         && s#0 != t#0
         && s#0 != u#0
       ==> read($Heap, s#0, _module.Node.val)
         == read($PreCallHeap#2, s#0, _module.Node.val);
    assume s#0 != null
         && s#0 != p#0
         && s#0 != q#0
         && s#0 != r#0
         && s#0 != s#0
         && s#0 != t#0
         && s#0 != u#0
       ==> read($Heap, s#0, _module.Node.tag)
         == read($PreCallHeap#2, s#0, _module.Node.tag);
    assume s#0 != null
         && s#0 != p#0
         && s#0 != q#0
         && s#0 != r#0
         && s#0 != s#0
         && s#0 != t#0
         && s#0 != u#0
       ==> read($Heap, s#0, _module.Node.score)
         == read($PreCallHeap#2, s#0, _module.Node.score);
    assume t#0 != null
         && t#0 != p#0
         && t#0 != q#0
         && t#0 != r#0
         && t#0 != s#0
         && t#0 != t#0
         && t#0 != u#0
       ==> read($Heap, t#0, _module.Node.val)
         == read($PreCallHeap#2, t#0, _module.Node.val);
    assume t#0 != null
         && t#0 != p#0
         && t#0 != q#0
         && t#0 != r#0
         && t#0 != s#0
         && t#0 != t#0
         && t#0 != u#0
       ==> read($Heap, t#0, _module.Node.tag)
         == read($PreCallHeap#2, t#0, _module.Node.tag);
    assume t#0 != null
         && t#0 != p#0
         && t#0 != q#0
         && t#0 != r#0
         && t#0 != s#0
         && t#0 != t#0
         && t#0 != u#0
       ==> read($Heap, t#0, _module.Node.score)
         == read($PreCallHeap#2, t#0, _module.Node.score);
    assume u#0 != null
         && u#0 != p#0
         && u#0 != q#0
         && u#0 != r#0
         && u#0 != s#0
         && u#0 != t#0
         && u#0 != u#0
       ==> read($Heap, u#0, _module.Node.val)
         == read($PreCallHeap#2, u#0, _module.Node.val);
    assume u#0 != null
         && u#0 != p#0
         && u#0 != q#0
         && u#0 != r#0
         && u#0 != s#0
         && u#0 != t#0
         && u#0 != u#0
       ==> read($Heap, u#0, _module.Node.tag)
         == read($PreCallHeap#2, u#0, _module.Node.tag);
    assume u#0 != null
         && u#0 != p#0
         && u#0 != q#0
         && u#0 != r#0
         && u#0 != s#0
         && u#0 != t#0
         && u#0 != u#0
       ==> read($Heap, u#0, _module.Node.score)
         == read($PreCallHeap#2, u#0, _module.Node.score);
    assume a#0 != null
         && a#0 != p#0
         && a#0 != q#0
         && a#0 != r#0
         && a#0 != s#0
         && a#0 != t#0
         && a#0 != u#0
       ==> read($Heap, a#0, _module.Node.val)
         == read($PreCallHeap#2, a#0, _module.Node.val);
    assume a#0 != null
         && a#0 != p#0
         && a#0 != q#0
         && a#0 != r#0
         && a#0 != s#0
         && a#0 != t#0
         && a#0 != u#0
       ==> read($Heap, a#0, _module.Node.tag)
         == read($PreCallHeap#2, a#0, _module.Node.tag);
    assume a#0 != null
         && a#0 != p#0
         && a#0 != q#0
         && a#0 != r#0
         && a#0 != s#0
         && a#0 != t#0
         && a#0 != u#0
       ==> read($Heap, a#0, _module.Node.score)
         == read($PreCallHeap#2, a#0, _module.Node.score);
    assume b#0 != null
         && b#0 != p#0
         && b#0 != q#0
         && b#0 != r#0
         && b#0 != s#0
         && b#0 != t#0
         && b#0 != u#0
       ==> read($Heap, b#0, _module.Node.val)
         == read($PreCallHeap#2, b#0, _module.Node.val);
    assume b#0 != null
         && b#0 != p#0
         && b#0 != q#0
         && b#0 != r#0
         && b#0 != s#0
         && b#0 != t#0
         && b#0 != u#0
       ==> read($Heap, b#0, _module.Node.tag)
         == read($PreCallHeap#2, b#0, _module.Node.tag);
    assume b#0 != null
         && b#0 != p#0
         && b#0 != q#0
         && b#0 != r#0
         && b#0 != s#0
         && b#0 != t#0
         && b#0 != u#0
       ==> read($Heap, b#0, _module.Node.score)
         == read($PreCallHeap#2, b#0, _module.Node.score);
    assume c#0 != null
         && c#0 != p#0
         && c#0 != q#0
         && c#0 != r#0
         && c#0 != s#0
         && c#0 != t#0
         && c#0 != u#0
       ==> read($Heap, c#0, _module.Node.val)
         == read($PreCallHeap#2, c#0, _module.Node.val);
    assume c#0 != null
         && c#0 != p#0
         && c#0 != q#0
         && c#0 != r#0
         && c#0 != s#0
         && c#0 != t#0
         && c#0 != u#0
       ==> read($Heap, c#0, _module.Node.tag)
         == read($PreCallHeap#2, c#0, _module.Node.tag);
    assume c#0 != null
         && c#0 != p#0
         && c#0 != q#0
         && c#0 != r#0
         && c#0 != s#0
         && c#0 != t#0
         && c#0 != u#0
       ==> read($Heap, c#0, _module.Node.score)
         == read($PreCallHeap#2, c#0, _module.Node.score);
    assume d#0 != null
         && d#0 != p#0
         && d#0 != q#0
         && d#0 != r#0
         && d#0 != s#0
         && d#0 != t#0
         && d#0 != u#0
       ==> read($Heap, d#0, _module.Node.val)
         == read($PreCallHeap#2, d#0, _module.Node.val);
    assume d#0 != null
         && d#0 != p#0
         && d#0 != q#0
         && d#0 != r#0
         && d#0 != s#0
         && d#0 != t#0
         && d#0 != u#0
       ==> read($Heap, d#0, _module.Node.tag)
         == read($PreCallHeap#2, d#0, _module.Node.tag);
    assume d#0 != null
         && d#0 != p#0
         && d#0 != q#0
         && d#0 != r#0
         && d#0 != s#0
         && d#0 != t#0
         && d#0 != u#0
       ==> read($Heap, d#0, _module.Node.score)
         == read($PreCallHeap#2, d#0, _module.Node.score);
    assume e#0 != null
         && e#0 != p#0
         && e#0 != q#0
         && e#0 != r#0
         && e#0 != s#0
         && e#0 != t#0
         && e#0 != u#0
       ==> read($Heap, e#0, _module.Node.val)
         == read($PreCallHeap#2, e#0, _module.Node.val);
    assume e#0 != null
         && e#0 != p#0
         && e#0 != q#0
         && e#0 != r#0
         && e#0 != s#0
         && e#0 != t#0
         && e#0 != u#0
       ==> read($Heap, e#0, _module.Node.tag)
         == read($PreCallHeap#2, e#0, _module.Node.tag);
    assume e#0 != null
         && e#0 != p#0
         && e#0 != q#0
         && e#0 != r#0
         && e#0 != s#0
         && e#0 != t#0
         && e#0 != u#0
       ==> read($Heap, e#0, _module.Node.score)
         == read($PreCallHeap#2, e#0, _module.Node.score);
    assume f#0 != null
         && f#0 != p#0
         && f#0 != q#0
         && f#0 != r#0
         && f#0 != s#0
         && f#0 != t#0
         && f#0 != u#0
       ==> read($Heap, f#0, _module.Node.val)
         == read($PreCallHeap#2, f#0, _module.Node.val);
    assume f#0 != null
         && f#0 != p#0
         && f#0 != q#0
         && f#0 != r#0
         && f#0 != s#0
         && f#0 != t#0
         && f#0 != u#0
       ==> read($Heap, f#0, _module.Node.tag)
         == read($PreCallHeap#2, f#0, _module.Node.tag);
    assume f#0 != null
         && f#0 != p#0
         && f#0 != q#0
         && f#0 != r#0
         && f#0 != s#0
         && f#0 != t#0
         && f#0 != u#0
       ==> read($Heap, f#0, _module.Node.score)
         == read($PreCallHeap#2, f#0, _module.Node.score);
    assume a##0 != null
         && a##0 != p#0
         && a##0 != q#0
         && a##0 != r#0
         && a##0 != s#0
         && a##0 != t#0
         && a##0 != u#0
       ==> read($Heap, a##0, _module.Node.val)
         == read($PreCallHeap#2, a##0, _module.Node.val);
    assume a##0 != null
         && a##0 != p#0
         && a##0 != q#0
         && a##0 != r#0
         && a##0 != s#0
         && a##0 != t#0
         && a##0 != u#0
       ==> read($Heap, a##0, _module.Node.tag)
         == read($PreCallHeap#2, a##0, _module.Node.tag);
    assume a##0 != null
         && a##0 != p#0
         && a##0 != q#0
         && a##0 != r#0
         && a##0 != s#0
         && a##0 != t#0
         && a##0 != u#0
       ==> read($Heap, a##0, _module.Node.score)
         == read($PreCallHeap#2, a##0, _module.Node.score);
    assume b##0 != null
         && b##0 != p#0
         && b##0 != q#0
         && b##0 != r#0
         && b##0 != s#0
         && b##0 != t#0
         && b##0 != u#0
       ==> read($Heap, b##0, _module.Node.val)
         == read($PreCallHeap#2, b##0, _module.Node.val);
    assume b##0 != null
         && b##0 != p#0
         && b##0 != q#0
         && b##0 != r#0
         && b##0 != s#0
         && b##0 != t#0
         && b##0 != u#0
       ==> read($Heap, b##0, _module.Node.tag)
         == read($PreCallHeap#2, b##0, _module.Node.tag);
    assume b##0 != null
         && b##0 != p#0
         && b##0 != q#0
         && b##0 != r#0
         && b##0 != s#0
         && b##0 != t#0
         && b##0 != u#0
       ==> read($Heap, b##0, _module.Node.score)
         == read($PreCallHeap#2, b##0, _module.Node.score);
    assume c##0 != null
         && c##0 != p#0
         && c##0 != q#0
         && c##0 != r#0
         && c##0 != s#0
         && c##0 != t#0
         && c##0 != u#0
       ==> read($Heap, c##0, _module.Node.val)
         == read($PreCallHeap#2, c##0, _module.Node.val);
    assume c##0 != null
         && c##0 != p#0
         && c##0 != q#0
         && c##0 != r#0
         && c##0 != s#0
         && c##0 != t#0
         && c##0 != u#0
       ==> read($Heap, c##0, _module.Node.tag)
         == read($PreCallHeap#2, c##0, _module.Node.tag);
    assume c##0 != null
         && c##0 != p#0
         && c##0 != q#0
         && c##0 != r#0
         && c##0 != s#0
         && c##0 != t#0
         && c##0 != u#0
       ==> read($Heap, c##0, _module.Node.score)
         == read($PreCallHeap#2, c##0, _module.Node.score);
    assume d##0 != null
         && d##0 != p#0
         && d##0 != q#0
         && d##0 != r#0
         && d##0 != s#0
         && d##0 != t#0
         && d##0 != u#0
       ==> read($Heap, d##0, _module.Node.val)
         == read($PreCallHeap#2, d##0, _module.Node.val);
    assume d##0 != null
         && d##0 != p#0
         && d##0 != q#0
         && d##0 != r#0
         && d##0 != s#0
         && d##0 != t#0
         && d##0 != u#0
       ==> read($Heap, d##0, _module.Node.tag)
         == read($PreCallHeap#2, d##0, _module.Node.tag);
    assume d##0 != null
         && d##0 != p#0
         && d##0 != q#0
         && d##0 != r#0
         && d##0 != s#0
         && d##0 != t#0
         && d##0 != u#0
       ==> read($Heap, d##0, _module.Node.score)
         == read($PreCallHeap#2, d##0, _module.Node.score);
    assume e##0 != null
         && e##0 != p#0
         && e##0 != q#0
         && e##0 != r#0
         && e##0 != s#0
         && e##0 != t#0
         && e##0 != u#0
       ==> read($Heap, e##0, _module.Node.val)
         == read($PreCallHeap#2, e##0, _module.Node.val);
    assume e##0 != null
         && e##0 != p#0
         && e##0 != q#0
         && e##0 != r#0
         && e##0 != s#0
         && e##0 != t#0
         && e##0 != u#0
       ==> read($Heap, e##0, _module.Node.tag)
         == read($PreCallHeap#2, e##0, _module.Node.tag);
    assume e##0 != null
         && e##0 != p#0
         && e##0 != q#0
         && e##0 != r#0
         && e##0 != s#0
         && e##0 != t#0
         && e##0 != u#0
       ==> read($Heap, e##0, _module.Node.score)
         == read($PreCallHeap#2, e##0, _module.Node.score);
    assume f##0 != null
         && f##0 != p#0
         && f##0 != q#0
         && f##0 != r#0
         && f##0 != s#0
         && f##0 != t#0
         && f##0 != u#0
       ==> read($Heap, f##0, _module.Node.val)
         == read($PreCallHeap#2, f##0, _module.Node.val);
    assume f##0 != null
         && f##0 != p#0
         && f##0 != q#0
         && f##0 != r#0
         && f##0 != s#0
         && f##0 != t#0
         && f##0 != u#0
       ==> read($Heap, f##0, _module.Node.tag)
         == read($PreCallHeap#2, f##0, _module.Node.tag);
    assume f##0 != null
         && f##0 != p#0
         && f##0 != q#0
         && f##0 != r#0
         && f##0 != s#0
         && f##0 != t#0
         && f##0 != u#0
       ==> read($Heap, f##0, _module.Node.score)
         == read($PreCallHeap#2, f##0, _module.Node.score);
    assume a##1 != null
         && a##1 != p#0
         && a##1 != q#0
         && a##1 != r#0
         && a##1 != s#0
         && a##1 != t#0
         && a##1 != u#0
       ==> read($Heap, a##1, _module.Node.val)
         == read($PreCallHeap#2, a##1, _module.Node.val);
    assume a##1 != null
         && a##1 != p#0
         && a##1 != q#0
         && a##1 != r#0
         && a##1 != s#0
         && a##1 != t#0
         && a##1 != u#0
       ==> read($Heap, a##1, _module.Node.tag)
         == read($PreCallHeap#2, a##1, _module.Node.tag);
    assume a##1 != null
         && a##1 != p#0
         && a##1 != q#0
         && a##1 != r#0
         && a##1 != s#0
         && a##1 != t#0
         && a##1 != u#0
       ==> read($Heap, a##1, _module.Node.score)
         == read($PreCallHeap#2, a##1, _module.Node.score);
    assume b##1 != null
         && b##1 != p#0
         && b##1 != q#0
         && b##1 != r#0
         && b##1 != s#0
         && b##1 != t#0
         && b##1 != u#0
       ==> read($Heap, b##1, _module.Node.val)
         == read($PreCallHeap#2, b##1, _module.Node.val);
    assume b##1 != null
         && b##1 != p#0
         && b##1 != q#0
         && b##1 != r#0
         && b##1 != s#0
         && b##1 != t#0
         && b##1 != u#0
       ==> read($Heap, b##1, _module.Node.tag)
         == read($PreCallHeap#2, b##1, _module.Node.tag);
    assume b##1 != null
         && b##1 != p#0
         && b##1 != q#0
         && b##1 != r#0
         && b##1 != s#0
         && b##1 != t#0
         && b##1 != u#0
       ==> read($Heap, b##1, _module.Node.score)
         == read($PreCallHeap#2, b##1, _module.Node.score);
    assume c##1 != null
         && c##1 != p#0
         && c##1 != q#0
         && c##1 != r#0
         && c##1 != s#0
         && c##1 != t#0
         && c##1 != u#0
       ==> read($Heap, c##1, _module.Node.val)
         == read($PreCallHeap#2, c##1, _module.Node.val);
    assume c##1 != null
         && c##1 != p#0
         && c##1 != q#0
         && c##1 != r#0
         && c##1 != s#0
         && c##1 != t#0
         && c##1 != u#0
       ==> read($Heap, c##1, _module.Node.tag)
         == read($PreCallHeap#2, c##1, _module.Node.tag);
    assume c##1 != null
         && c##1 != p#0
         && c##1 != q#0
         && c##1 != r#0
         && c##1 != s#0
         && c##1 != t#0
         && c##1 != u#0
       ==> read($Heap, c##1, _module.Node.score)
         == read($PreCallHeap#2, c##1, _module.Node.score);
    assume d##1 != null
         && d##1 != p#0
         && d##1 != q#0
         && d##1 != r#0
         && d##1 != s#0
         && d##1 != t#0
         && d##1 != u#0
       ==> read($Heap, d##1, _module.Node.val)
         == read($PreCallHeap#2, d##1, _module.Node.val);
    assume d##1 != null
         && d##1 != p#0
         && d##1 != q#0
         && d##1 != r#0
         && d##1 != s#0
         && d##1 != t#0
         && d##1 != u#0
       ==> read($Heap, d##1, _module.Node.tag)
         == read($PreCallHeap#2, d##1, _module.Node.tag);
    assume d##1 != null
         && d##1 != p#0
         && d##1 != q#0
         && d##1 != r#0
         && d##1 != s#0
         && d##1 != t#0
         && d##1 != u#0
       ==> read($Heap, d##1, _module.Node.score)
         == read($PreCallHeap#2, d##1, _module.Node.score);
    assume e##1 != null
         && e##1 != p#0
         && e##1 != q#0
         && e##1 != r#0
         && e##1 != s#0
         && e##1 != t#0
         && e##1 != u#0
       ==> read($Heap, e##1, _module.Node.val)
         == read($PreCallHeap#2, e##1, _module.Node.val);
    assume e##1 != null
         && e##1 != p#0
         && e##1 != q#0
         && e##1 != r#0
         && e##1 != s#0
         && e##1 != t#0
         && e##1 != u#0
       ==> read($Heap, e##1, _module.Node.tag)
         == read($PreCallHeap#2, e##1, _module.Node.tag);
    assume e##1 != null
         && e##1 != p#0
         && e##1 != q#0
         && e##1 != r#0
         && e##1 != s#0
         && e##1 != t#0
         && e##1 != u#0
       ==> read($Heap, e##1, _module.Node.score)
         == read($PreCallHeap#2, e##1, _module.Node.score);
    assume f##1 != null
         && f##1 != p#0
         && f##1 != q#0
         && f##1 != r#0
         && f##1 != s#0
         && f##1 != t#0
         && f##1 != u#0
       ==> read($Heap, f##1, _module.Node.val)
         == read($PreCallHeap#2, f##1, _module.Node.val);
    assume f##1 != null
         && f##1 != p#0
         && f##1 != q#0
         && f##1 != r#0
         && f##1 != s#0
         && f##1 != t#0
         && f##1 != u#0
       ==> read($Heap, f##1, _module.Node.tag)
         == read($PreCallHeap#2, f##1, _module.Node.tag);
    assume f##1 != null
         && f##1 != p#0
         && f##1 != q#0
         && f##1 != r#0
         && f##1 != s#0
         && f##1 != t#0
         && f##1 != u#0
       ==> read($Heap, f##1, _module.Node.score)
         == read($PreCallHeap#2, f##1, _module.Node.score);
    assume a##2 != null
         && a##2 != p#0
         && a##2 != q#0
         && a##2 != r#0
         && a##2 != s#0
         && a##2 != t#0
         && a##2 != u#0
       ==> read($Heap, a##2, _module.Node.val)
         == read($PreCallHeap#2, a##2, _module.Node.val);
    assume a##2 != null
         && a##2 != p#0
         && a##2 != q#0
         && a##2 != r#0
         && a##2 != s#0
         && a##2 != t#0
         && a##2 != u#0
       ==> read($Heap, a##2, _module.Node.tag)
         == read($PreCallHeap#2, a##2, _module.Node.tag);
    assume a##2 != null
         && a##2 != p#0
         && a##2 != q#0
         && a##2 != r#0
         && a##2 != s#0
         && a##2 != t#0
         && a##2 != u#0
       ==> read($Heap, a##2, _module.Node.score)
         == read($PreCallHeap#2, a##2, _module.Node.score);
    assume b##2 != null
         && b##2 != p#0
         && b##2 != q#0
         && b##2 != r#0
         && b##2 != s#0
         && b##2 != t#0
         && b##2 != u#0
       ==> read($Heap, b##2, _module.Node.val)
         == read($PreCallHeap#2, b##2, _module.Node.val);
    assume b##2 != null
         && b##2 != p#0
         && b##2 != q#0
         && b##2 != r#0
         && b##2 != s#0
         && b##2 != t#0
         && b##2 != u#0
       ==> read($Heap, b##2, _module.Node.tag)
         == read($PreCallHeap#2, b##2, _module.Node.tag);
    assume b##2 != null
         && b##2 != p#0
         && b##2 != q#0
         && b##2 != r#0
         && b##2 != s#0
         && b##2 != t#0
         && b##2 != u#0
       ==> read($Heap, b##2, _module.Node.score)
         == read($PreCallHeap#2, b##2, _module.Node.score);
    assume c##2 != null
         && c##2 != p#0
         && c##2 != q#0
         && c##2 != r#0
         && c##2 != s#0
         && c##2 != t#0
         && c##2 != u#0
       ==> read($Heap, c##2, _module.Node.val)
         == read($PreCallHeap#2, c##2, _module.Node.val);
    assume c##2 != null
         && c##2 != p#0
         && c##2 != q#0
         && c##2 != r#0
         && c##2 != s#0
         && c##2 != t#0
         && c##2 != u#0
       ==> read($Heap, c##2, _module.Node.tag)
         == read($PreCallHeap#2, c##2, _module.Node.tag);
    assume c##2 != null
         && c##2 != p#0
         && c##2 != q#0
         && c##2 != r#0
         && c##2 != s#0
         && c##2 != t#0
         && c##2 != u#0
       ==> read($Heap, c##2, _module.Node.score)
         == read($PreCallHeap#2, c##2, _module.Node.score);
    assume d##2 != null
         && d##2 != p#0
         && d##2 != q#0
         && d##2 != r#0
         && d##2 != s#0
         && d##2 != t#0
         && d##2 != u#0
       ==> read($Heap, d##2, _module.Node.val)
         == read($PreCallHeap#2, d##2, _module.Node.val);
    assume d##2 != null
         && d##2 != p#0
         && d##2 != q#0
         && d##2 != r#0
         && d##2 != s#0
         && d##2 != t#0
         && d##2 != u#0
       ==> read($Heap, d##2, _module.Node.tag)
         == read($PreCallHeap#2, d##2, _module.Node.tag);
    assume d##2 != null
         && d##2 != p#0
         && d##2 != q#0
         && d##2 != r#0
         && d##2 != s#0
         && d##2 != t#0
         && d##2 != u#0
       ==> read($Heap, d##2, _module.Node.score)
         == read($PreCallHeap#2, d##2, _module.Node.score);
    assume e##2 != null
         && e##2 != p#0
         && e##2 != q#0
         && e##2 != r#0
         && e##2 != s#0
         && e##2 != t#0
         && e##2 != u#0
       ==> read($Heap, e##2, _module.Node.val)
         == read($PreCallHeap#2, e##2, _module.Node.val);
    assume e##2 != null
         && e##2 != p#0
         && e##2 != q#0
         && e##2 != r#0
         && e##2 != s#0
         && e##2 != t#0
         && e##2 != u#0
       ==> read($Heap, e##2, _module.Node.tag)
         == read($PreCallHeap#2, e##2, _module.Node.tag);
    assume e##2 != null
         && e##2 != p#0
         && e##2 != q#0
         && e##2 != r#0
         && e##2 != s#0
         && e##2 != t#0
         && e##2 != u#0
       ==> read($Heap, e##2, _module.Node.score)
         == read($PreCallHeap#2, e##2, _module.Node.score);
    assume f##2 != null
         && f##2 != p#0
         && f##2 != q#0
         && f##2 != r#0
         && f##2 != s#0
         && f##2 != t#0
         && f##2 != u#0
       ==> read($Heap, f##2, _module.Node.val)
         == read($PreCallHeap#2, f##2, _module.Node.val);
    assume f##2 != null
         && f##2 != p#0
         && f##2 != q#0
         && f##2 != r#0
         && f##2 != s#0
         && f##2 != t#0
         && f##2 != u#0
       ==> read($Heap, f##2, _module.Node.tag)
         == read($PreCallHeap#2, f##2, _module.Node.tag);
    assume f##2 != null
         && f##2 != p#0
         && f##2 != q#0
         && f##2 != r#0
         && f##2 != s#0
         && f##2 != t#0
         && f##2 != u#0
       ==> read($Heap, f##2, _module.Node.score)
         == read($PreCallHeap#2, f##2, _module.Node.score);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "Test/arith.dfy(133,30)"} true;
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

procedure {:verboseName "Node._ctor (well-formedness)"} CheckWellFormed$$_module.Node.__ctor(v#0: int, t#0: int, s#0: int) returns (this: ref);
  modifies $Heap, $Alloc;



procedure {:verboseName "Node._ctor (call)"} Call$$_module.Node.__ctor(v#0: int, t#0: int, s#0: int)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && (this == null || $Alloc[this]));
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id1200"} $Unbox(read($Heap, this, _module.Node.val)): int == v#0;
  free ensures {:always_assume} true;
  ensures {:id "id1201"} $Unbox(read($Heap, this, _module.Node.tag)): int == t#0;
  free ensures {:always_assume} true;
  ensures {:id "id1202"} $Unbox(read($Heap, this, _module.Node.score)): int == s#0;
  // constructor allocates the object
  ensures !old($Alloc)[this];



procedure {:verboseName "Node._ctor (correctness)"} Impl$$_module.Node.__ctor(v#0: int, t#0: int, s#0: int) returns (this: ref, $_reverifyPost: bool);
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id1203"} $Unbox(read($Heap, this, _module.Node.val)): int == v#0;
  free ensures {:always_assume} true;
  ensures {:id "id1204"} $Unbox(read($Heap, this, _module.Node.tag)): int == t#0;
  free ensures {:always_assume} true;
  ensures {:id "id1205"} $Unbox(read($Heap, this, _module.Node.score)): int == s#0;



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

implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Node._ctor (correctness)"} Impl$$_module.Node.__ctor(v#0: int, t#0: int, s#0: int) returns (this: ref, $_reverifyPost: bool)
{
  var this.val: int;
  var this.tag: int;
  var this.score: int;

    // AddMethodImpl: _ctor, Impl$$_module.Node.__ctor
    assume {:captureState "Test/arith.dfy(8,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/saline/development/projects/dafny/Test/arith.dfy(8,3)
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(8,9)
    assume true;
    assume true;
    assume true;
    this.val := v#0;
    assume {:captureState "Test/arith.dfy(8,12)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(8,19)
    assume true;
    assume true;
    assume true;
    this.tag := t#0;
    assume {:captureState "Test/arith.dfy(8,22)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/arith.dfy(8,31)
    assume true;
    assume true;
    assume true;
    this.score := s#0;
    assume {:captureState "Test/arith.dfy(8,34)"} true;
    // ----- new; ----- /Users/saline/development/projects/dafny/Test/arith.dfy(8,3)
    assume this != null && $Is(this, Tclass._module.Node?());
    assume !$Alloc[this];
    assume $Unbox(read($Heap, this, _module.Node.val)): int == this.val;
    assume $Unbox(read($Heap, this, _module.Node.tag)): int == this.tag;
    assume $Unbox(read($Heap, this, _module.Node.score)): int == this.score;
    $Alloc := $Alloc[this := true];
    assume true;
    // ----- divided block after new; ----- /Users/saline/development/projects/dafny/Test/arith.dfy(8,3)
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
