
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

procedure {:verboseName "Add (well-formedness)"} CheckWellFormed$$_module.__default.Add(x#0: int, 
    s#0: Set where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap))
   returns (r#0: Set where $Is(r#0, TSet(TInt)) && $IsAlloc(r#0, TSet(TInt), $Heap));
  modifies $Heap, $Alloc;



procedure {:verboseName "Add (call)"} Call$$_module.__default.Add(x#0: int, 
    s#0: Set where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap))
   returns (r#0: Set where $Is(r#0, TSet(TInt)) && $IsAlloc(r#0, TSet(TInt), $Heap));
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id2"} Set#Equal(r#0, Set#Union(s#0, Set#UnionOne(Set#Empty(): Set, $Box(x#0))));
  free ensures {:always_assume} true;
  ensures {:id "id3"} Set#IsMember(r#0, $Box(x#0));



procedure {:verboseName "Add (correctness)"} Impl$$_module.__default.Add(x#0: int, 
    s#0: Set where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap))
   returns (defass#r#0: bool, 
    r#0: Set
       where defass#r#0 ==> $Is(r#0, TSet(TInt)) && $IsAlloc(r#0, TSet(TInt), $Heap), 
    $_reverifyPost: bool);
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id4"} Set#Equal(r#0, Set#Union(s#0, Set#UnionOne(Set#Empty(): Set, $Box(x#0))));
  free ensures {:always_assume} true;
  ensures {:id "id5"} Set#IsMember(r#0, $Box(x#0));



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Add (correctness)"} Impl$$_module.__default.Add(x#0: int, s#0: Set) returns (defass#r#0: bool, r#0: Set, $_reverifyPost: bool)
{
    // AddMethodImpl: Add, Impl$$_module.__default.Add
    assume {:captureState "Test/ds.dfy(4,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/ds.dfy(5,5)
    assume true;
    assume true;
    r#0 := Set#Union(s#0, Set#UnionOne(Set#Empty(): Set, $Box(x#0)));
    defass#r#0 := true;
    assume {:captureState "Test/ds.dfy(5,14)"} true;
    assert {:id "id7"} defass#r#0;
}



procedure {:verboseName "Count (well-formedness)"} CheckWellFormed$$_module.__default.Count(s#0: Set where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap))
   returns (n#0: int where LitInt(0) <= n#0);
  modifies $Heap, $Alloc;



procedure {:verboseName "Count (call)"} Call$$_module.__default.Count(s#0: Set where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap))
   returns (n#0: int where LitInt(0) <= n#0);
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id9"} n#0 == Set#Card(s#0);



procedure {:verboseName "Count (correctness)"} Impl$$_module.__default.Count(s#0: Set where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap))
   returns (defass#n#0: bool, 
    n#0: int where defass#n#0 ==> LitInt(0) <= n#0, 
    $_reverifyPost: bool);
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id10"} n#0 == Set#Card(s#0);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Count (correctness)"} Impl$$_module.__default.Count(s#0: Set) returns (defass#n#0: bool, n#0: int, $_reverifyPost: bool)
{
  var defass#x#0: bool;
  var x#0: int;
  var x#1: int;
  var subCount#0: int where LitInt(0) <= subCount#0;
  var $rhs##0: int;
  var s##0: Set;
  var $PreCallHeap#0: Heap;
  var $PreCallAlloc#0: [ref]bool;

    // AddMethodImpl: Count, Impl$$_module.__default.Count
    assume {:captureState "Test/ds.dfy(27,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/saline/development/projects/dafny/Test/ds.dfy(28,3)
    assume true;
    if (Set#Equal(s#0, Set#Empty(): Set))
    {
        push;
        // ----- return statement ----- /Users/saline/development/projects/dafny/Test/ds.dfy(29,5)
        // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/ds.dfy(29,5)
        assume true;
        assert {:id "id11"} $Is(LitInt(0), Tclass._System.nat());
        assume true;
        n#0 := LitInt(0);
        defass#n#0 := true;
        assume {:captureState "Test/ds.dfy(29,12)"} true;
        assert {:id "id13"} defass#n#0;
        pop;
        return;

        pop;
    }
    else
    {
    }

    // ----- assign-such-that statement ----- /Users/saline/development/projects/dafny/Test/ds.dfy(32,9)
    havoc x#1;
    if (true)
    {
        assume true;
    }

    assert {:id "id14"} ($Is(LitInt(0), TInt) && Set#IsMember(s#0, $Box(LitInt(0))))
       || (exists $as#x0#0: int :: 
        { Set#IsMember(s#0, $Box($as#x0#0)) } 
        Set#IsMember(s#0, $Box($as#x0#0)));
    defass#x#0 := true;
    havoc x#0;
    assume {:id "id15"} Set#IsMember(s#0, $Box(x#0));
    assume {:captureState "Test/ds.dfy(32,17)"} true;
    // ----- call statement ----- /Users/saline/development/projects/dafny/Test/ds.dfy(33,24)
    assume true;
    // TrCallStmt: Adding lhs with type nat
    // TrCallStmt: Before ProcessCallStmt
    assert {:id "id16"} defass#x#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    s##0 := Set#Difference(s#0, Set#UnionOne(Set#Empty(): Set, $Box(x#0)));
    $PreCallHeap#0 := $Heap;
    $PreCallAlloc#0 := $Alloc;
    assume true;
    assert {:id "id17"} Set#Subset(s##0, s#0) && !Set#Subset(s#0, s##0);
    call {:id "id18"} $rhs##0 := Call$$_module.__default.Count(s##0);
    // qf-call-frame Count: supports=0 reads=0 modified=0
    // TrCallStmt: After ProcessCallStmt
    subCount#0 := $rhs##0;
    assume {:captureState "Test/ds.dfy(33,32)"} true;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/ds.dfy(35,5)
    assume true;
    assert {:id "id20"} $Is(1 + subCount#0, Tclass._System.nat());
    assume true;
    n#0 := 1 + subCount#0;
    defass#n#0 := true;
    assume {:captureState "Test/ds.dfy(35,19)"} true;
    assert {:id "id22"} defass#n#0;
}



const unique class._module.Bag?: ClassName;

const _module.Bag.contents: Field
uses {
axiom FDim(_module.Bag.contents) == 0
   && FieldOfDecl(class._module.Bag?, field$contents) == _module.Bag.contents
   && $IsGhostField(_module.Bag.contents);
}

procedure {:verboseName "Bag._ctor (well-formedness)"} CheckWellFormed$$_module.Bag.__ctor() returns (this: ref);
  modifies $Heap, $Alloc;



function Tclass._module.Bag() : Ty
uses {
// Tclass._module.Bag Tag
axiom Tag(Tclass._module.Bag()) == Tagclass._module.Bag
   && TagFamily(Tclass._module.Bag()) == tytagFamily$Bag;
}

const unique Tagclass._module.Bag: TyTag;

// Box/unbox axiom for Tclass._module.Bag
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Bag()) } 
  $IsBox(bx, Tclass._module.Bag()) ==> $Box($Unbox(bx): ref) == bx);

procedure {:verboseName "Bag._ctor (call)"} Call$$_module.Bag.__ctor()
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Bag())
         && (this == null || $Alloc[this]));
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id24"} Set#Equal($Unbox(read($Heap, this, _module.Bag.contents)): Set, Set#Empty(): Set);
  // constructor allocates the object
  ensures !old($Alloc)[this];



procedure {:verboseName "Bag._ctor (correctness)"} Impl$$_module.Bag.__ctor() returns (this: ref, $_reverifyPost: bool);
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id25"} Set#Equal($Unbox(read($Heap, this, _module.Bag.contents)): Set, Set#Empty(): Set);



function Tclass._module.Bag?() : Ty
uses {
// Tclass._module.Bag? Tag
axiom Tag(Tclass._module.Bag?()) == Tagclass._module.Bag?
   && TagFamily(Tclass._module.Bag?()) == tytagFamily$Bag;
}

const unique Tagclass._module.Bag?: TyTag;

// Box/unbox axiom for Tclass._module.Bag?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Bag?()) } 
  $IsBox(bx, Tclass._module.Bag?()) ==> $Box($Unbox(bx): ref) == bx);

implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Bag._ctor (correctness)"} Impl$$_module.Bag.__ctor() returns (this: ref, $_reverifyPost: bool)
{
  var this.contents: Set;

    // AddMethodImpl: _ctor, Impl$$_module.Bag.__ctor
    assume {:captureState "Test/ds.dfy(13,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/saline/development/projects/dafny/Test/ds.dfy(13,3)
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/ds.dfy(14,14)
    assume true;
    assume true;
    assume true;
    this.contents := Lit(Set#Empty(): Set);
    assume {:captureState "Test/ds.dfy(14,18)"} true;
    // ----- new; ----- /Users/saline/development/projects/dafny/Test/ds.dfy(13,3)
    assume this != null && $Is(this, Tclass._module.Bag?());
    assume !$Alloc[this];
    assume $Unbox(read($Heap, this, _module.Bag.contents)): Set == this.contents;
    $Alloc := $Alloc[this := true];
    assume true;
    // ----- divided block after new; ----- /Users/saline/development/projects/dafny/Test/ds.dfy(13,3)
}



procedure {:verboseName "Bag.Add (well-formedness)"} CheckWellFormed$$_module.Bag.Add(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Bag())
         && (this == null || $Alloc[this]), 
    x#0: int);
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Bag.Add (well-formedness)"} CheckWellFormed$$_module.Bag.Add(this: ref, x#0: int)
{

    // AddMethodImpl: Add, CheckWellFormed$$_module.Bag.Add
    assume {:captureState "Test/ds.dfy(17,9): initial state"} true;
    havoc $Heap;
    assume {:captureState "Test/ds.dfy(19,21): post-state"} true;
    assume true;
    assert {:id "id27"} this == null || old($Alloc)[this];
    assume true;
    assume {:id "id28"} Set#Equal($Unbox(read($Heap, this, _module.Bag.contents)): Set, 
      Set#Union($Unbox(read(old($Heap), this, _module.Bag.contents)): Set, 
        Set#UnionOne(Set#Empty(): Set, $Box(x#0))));
}



procedure {:verboseName "Bag.Add (call)"} Call$$_module.Bag.Add(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Bag())
         && (this == null || $Alloc[this]), 
    x#0: int);
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id29"} Set#Equal($Unbox(read($Heap, this, _module.Bag.contents)): Set, 
    Set#Union($Unbox(read(old($Heap), this, _module.Bag.contents)): Set, 
      Set#UnionOne(Set#Empty(): Set, $Box(x#0))));



procedure {:verboseName "Bag.Add (correctness)"} Impl$$_module.Bag.Add(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Bag())
         && (this == null || $Alloc[this]), 
    x#0: int)
   returns ($_reverifyPost: bool);
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap, $Alloc;
  // user-defined postconditions
  free ensures {:always_assume} true;
  ensures {:id "id30"} Set#Equal($Unbox(read($Heap, this, _module.Bag.contents)): Set, 
    Set#Union($Unbox(read(old($Heap), this, _module.Bag.contents)): Set, 
      Set#UnionOne(Set#Empty(): Set, $Box(x#0))));



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Bag.Add (correctness)"} Impl$$_module.Bag.Add(this: ref, x#0: int) returns ($_reverifyPost: bool)
{
  var $rhs#0: Set;

    // AddMethodImpl: Add, Impl$$_module.Bag.Add
    assume {:captureState "Test/ds.dfy(20,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/Test/ds.dfy(21,14)
    assume true;
    assume true;
    assume true;
    assume true;
    $rhs#0 := Set#Union($Unbox(read($Heap, this, _module.Bag.contents)): Set, 
      Set#UnionOne(Set#Empty(): Set, $Box(x#0)));
    $Heap := update($Heap, this, _module.Bag.contents, $Box($rhs#0));
    assume true;
    assume {:captureState "Test/ds.dfy(21,30)"} true;
}



// $Is axiom for non-null type _module.Bag
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Bag()) } { $Is(c#0, Tclass._module.Bag?()) } 
  $Is(c#0, Tclass._module.Bag())
     <==> $Is(c#0, Tclass._module.Bag?()) && c#0 != null);

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

const unique tytagFamily$Bag: TyTagFamily;

const unique field$contents: NameFamily;
