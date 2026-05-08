const $$Language$Dafny: bool uses {  // To be recognizable to the ModelViewer as
  axiom $$Language$Dafny;            // coming from a Dafny program.
}

// ---------------------------------------------------------------
// -- Types ------------------------------------------------------
// ---------------------------------------------------------------

type Ty;
type Bv0 = int;

const unique TBool : Ty uses {
  axiom Tag(TBool) == TagBool;
}
const unique TChar : Ty uses {
  axiom Tag(TChar) == TagChar;
}
const unique TInt  : Ty uses {
  axiom Tag(TInt) == TagInt;
}
const unique TField: Ty uses {
  axiom Tag(TField) == TagField;
}
const unique TReal : Ty uses {
  axiom Tag(TReal) == TagReal;
}
const unique TORDINAL  : Ty uses {
  axiom Tag(TORDINAL) == TagORDINAL;
}
// See for which axioms we can make use of the trigger to determine the connection.
function TBitvector(int) : Ty;

function TSet(Ty) : Ty;

function TISet(Ty) : Ty;

function TMultiSet(Ty) : Ty;

function TSeq(Ty) : Ty;

function TMap(Ty, Ty) : Ty;

function TIMap(Ty, Ty) : Ty;


function Inv0_TBitvector(Ty) : int;
function Inv0_TSet(Ty) : Ty;
function Inv0_TISet(Ty) : Ty;
function Inv0_TSeq(Ty) : Ty;
function Inv0_TMultiSet(Ty) : Ty;
function Inv0_TMap(Ty) : Ty;
function Inv1_TMap(Ty) : Ty;
function Inv0_TIMap(Ty) : Ty;
function Inv1_TIMap(Ty) : Ty;

// -- Classes and Datatypes --

// -- Type Tags --
type TyTag;
function Tag(Ty) : TyTag;

const unique TagBool     : TyTag;
const unique TagChar     : TyTag;
const unique TagInt      : TyTag;
const unique TagField    : TyTag;
const unique TagReal     : TyTag;
const unique TagORDINAL  : TyTag;
const unique TagSet      : TyTag;
const unique TagISet     : TyTag;
const unique TagMultiSet : TyTag;
const unique TagSeq      : TyTag;
const unique TagMap      : TyTag;
const unique TagIMap     : TyTag;
const unique TagClass    : TyTag;

type TyTagFamily;
function TagFamily(Ty): TyTagFamily;

// ---------------------------------------------------------------
// -- Literals ---------------------------------------------------
// ---------------------------------------------------------------
function {:identity} Lit<T>(x: T): T { x }
axiom (forall<T> x: T :: { $Box(Lit(x)) } $Box(Lit(x)) == Lit($Box(x)) );

// Specialize Lit to concrete types.
// These aren't logically required, but on some examples improve
// verification speed
function {:identity} LitInt(x: int): int { x }
axiom (forall x: int :: { $Box(LitInt(x)) } $Box(LitInt(x)) == Lit($Box(x)) );

function {:identity} LitReal(x: real): real { x }
axiom (forall x: real :: { $Box(LitReal(x)) } $Box(LitReal(x)) == Lit($Box(x)) );

// ---------------------------------------------------------------
// -- Characters -------------------------------------------------
// ---------------------------------------------------------------

#if UNICODE_CHAR
function {:inline} char#IsChar(n: int): bool {
  (0                  <= n && n < 55296   /* 0xD800 */) ||
  (57344 /* 0xE000 */ <= n && n < 1114112 /* 0x11_0000 */ )
}
#else
function {:inline} char#IsChar(n: int): bool {
  0 <= n && n < 65536
}
#endif

type char;
function char#FromInt(int): char;
axiom (forall n: int ::
  { char#FromInt(n) }
  char#IsChar(n) ==> char#ToInt(char#FromInt(n)) == n);

function char#ToInt(char): int;
axiom (forall ch: char ::
  { char#ToInt(ch) }
  char#FromInt(char#ToInt(ch)) == ch &&
  char#IsChar(char#ToInt(ch)));

function char#Plus(char, char): char;
axiom (forall a: char, b: char ::
  { char#Plus(a, b) }
  char#Plus(a, b) == char#FromInt(char#ToInt(a) + char#ToInt(b)));

function char#Minus(char, char): char;
axiom (forall a: char, b: char ::
  { char#Minus(a, b) }
  char#Minus(a, b) == char#FromInt(char#ToInt(a) - char#ToInt(b)));

// ---------------------------------------------------------------
// -- References -------------------------------------------------
// ---------------------------------------------------------------

type ref;

const null: ref;
const locals: ref;

type FieldFamily;
const unique object_field: FieldFamily;

// local_field keeps the information about the depth and the field family

function field_depth(f: Field): int;
function field_family(f: Field): FieldFamily;

function local_field(ff: FieldFamily, depth: int): Field
uses {
  axiom (forall ff: FieldFamily, depth: int ::
    {:trigger local_field(ff, depth)}
    field_depth(local_field(ff, depth)) == depth
    && field_family(local_field(ff, depth)) == ff
  );
}

// ---------------------------------------------------------------
// -- Boxing and unboxing ----------------------------------------
// ---------------------------------------------------------------

type Box;
const $ArbitraryBoxValue: Box;

function $Box<T>(T): Box;
function $Unbox<T>(Box): T;
axiom (forall<T> x : T   :: { $Box(x) } {:weight 3} $Unbox($Box(x)) == x);
axiom (forall<T> x : Box :: { $Unbox(x): T}      $Box($Unbox(x): T) == x);


// Corresponding entries for boxes...
// This could probably be solved by having Box also inhabit Ty
function $IsBox(Box,Ty): bool;
function $IsAllocBox(Box,Ty,Heap): bool;

axiom (forall bx : Box ::
    { $IsBox(bx, TInt) }
    ( $IsBox(bx, TInt) ==> $Box($Unbox(bx) : int) == bx && $Is($Unbox(bx) : int, TInt)));
axiom (forall bx : Box ::
    { $IsBox(bx, TReal) }
    ( $IsBox(bx, TReal) ==> $Box($Unbox(bx) : real) == bx && $Is($Unbox(bx) : real, TReal)));
axiom (forall bx : Box ::
    { $IsBox(bx, TBool) }
    ( $IsBox(bx, TBool) ==> $Box($Unbox(bx) : bool) == bx && $Is($Unbox(bx) : bool, TBool)));
axiom (forall bx : Box ::
    { $IsBox(bx, TChar) }
    ( $IsBox(bx, TChar) ==> $Box($Unbox(bx) : char) == bx && $Is($Unbox(bx) : char, TChar)));

// Since each bitvector type is a separate type in Boogie, the Box/Unbox axioms for bitvectors are
// generated programmatically. Except, Bv0 is given here.
axiom (forall bx : Box ::
    { $IsBox(bx, TBitvector(0)) }
    ( $IsBox(bx, TBitvector(0)) ==> $Box($Unbox(bx) : Bv0) == bx && $Is($Unbox(bx) : Bv0, TBitvector(0))));

axiom (forall<T> v : T, t : Ty ::
    { $IsBox($Box(v), t) }
    ( $IsBox($Box(v), t) <==> $Is(v,t) ));

// ---------------------------------------------------------------
// -- Is and IsAlloc ---------------------------------------------
// ---------------------------------------------------------------

// Type-argument to $Is is the /representation type/,
// the second value argument to $Is is the actual type.
function $Is<T>(T,Ty): bool;           // no heap for now
axiom(forall v : int  :: { $Is(v,TInt) }  $Is(v,TInt));
axiom(forall v : real :: { $Is(v,TReal) } $Is(v,TReal));
axiom(forall v : bool :: { $Is(v,TBool) } $Is(v,TBool));
axiom(forall v : char :: { $Is(v,TChar) } $Is(v,TChar));
axiom(forall v : Field :: { $Is(v,TField) } $Is(v,TField));
axiom(forall v : ORDINAL :: { $Is(v,TORDINAL) } $Is(v,TORDINAL));

// Since every bitvector type is a separate type in Boogie, the $Is/$IsAlloc axioms
// for bitvectors are generated programatically. Except, TBitvector(0) is given here.
axiom (forall v: Bv0 :: { $Is(v, TBitvector(0)) } $Is(v, TBitvector(0)));

function $IsAlloc<T>(T,Ty,Heap): bool;
function $AlwaysAllocated(Ty): bool;

function $OlderTag(Heap): bool;

// ---------------------------------------------------------------
// -- Encoding of type names -------------------------------------
// ---------------------------------------------------------------

type ClassName;
const unique class._System.int: ClassName;
const unique class._System.bool: ClassName;
const unique class._System.set: ClassName;
const unique class._System.seq: ClassName;
const unique class._System.multiset: ClassName;

function Tclass._System.object?(): Ty;
function Tclass._System.Tuple2(Ty, Ty): Ty;

function /*{:never_pattern true}*/ dtype(ref): Ty; // changed from ClassName to Ty

function TypeTuple(a: ClassName, b: ClassName): ClassName;
function TypeTupleCar(ClassName): ClassName;
function TypeTupleCdr(ClassName): ClassName;
// TypeTuple is injective in both arguments:
axiom (forall a: ClassName, b: ClassName :: { TypeTuple(a,b) }
  TypeTupleCar(TypeTuple(a,b)) == a &&
  TypeTupleCdr(TypeTuple(a,b)) == b);

// -- Function handles -------------------------------------------

type HandleType;

function SetRef_to_SetBox(s: [ref]bool): Set;

// Functions ApplyN, RequiresN, and ReadsN are generated on demand by the translator,
// but Apply1 is referred to in the prelude, so its definition is hardcoded here.
function Apply1(Ty, Ty, Heap, HandleType, Box): Box;

// In p3, the translator does not emit the usual arrow-handle declarations.
// Keep inert stubs here so built-in arrow/function encodings that still mention
// these names can resolve without reintroducing the full quantified machinery.
function Requires0(Ty, Heap, HandleType): bool;
function Requires1(Ty, Ty, Heap, HandleType, Box): bool;
function Requires2(Ty, Ty, Ty, Heap, HandleType, Box, Box): bool;
function Reads0(Ty, Heap, HandleType): Set;
function Reads1(Ty, Ty, Heap, HandleType, Box): Set;
function Reads2(Ty, Ty, Ty, Heap, HandleType, Box, Box): Set;
function Requires0#canCall(Ty, Heap, HandleType): bool;
function Requires1#canCall(Ty, Ty, Heap, HandleType, Box): bool;
function Requires2#canCall(Ty, Ty, Ty, Heap, HandleType, Box, Box): bool;

// ---------------------------------------------------------------
// -- Datatypes --------------------------------------------------
// ---------------------------------------------------------------

type DatatypeType;

type DtCtorId;
function DatatypeCtorId(DatatypeType): DtCtorId;

function DtRank(DatatypeType): int;
function BoxRank(Box): int;

axiom (forall d: DatatypeType :: {BoxRank($Box(d))} BoxRank($Box(d)) == DtRank(d));

// ---------------------------------------------------------------
// -- Big Ordinals -----------------------------------------------
// ---------------------------------------------------------------

type ORDINAL = Box;  // :| There are more big ordinals than boxes

function ORD#IsNat(ORDINAL): bool;
function ORD#Offset(ORDINAL): int;

function {:inline} ORD#IsLimit(o: ORDINAL): bool { ORD#Offset(o) == 0 }
function {:inline} ORD#IsSucc(o: ORDINAL): bool { 0 < ORD#Offset(o) }

function ORD#FromNat(int): ORDINAL;

function ORD#Less(ORDINAL, ORDINAL): bool;

function ORD#LessThanLimit(ORDINAL, ORDINAL): bool;

function ORD#Plus(ORDINAL, ORDINAL): ORDINAL;

function ORD#Minus(ORDINAL, ORDINAL): ORDINAL;

// ---------------------------------------------------------------
// -- Layers of function encodings -------------------------------
// ---------------------------------------------------------------

type LayerType;
const $LZ: LayerType;
function $LS(LayerType): LayerType;
function AsFuelBottom(LayerType) : LayerType;

function AtLayer<A>([LayerType]A, LayerType): A;
axiom (forall<A> f : [LayerType]A, ly : LayerType :: { AtLayer(f,ly) } AtLayer(f,ly) == f[ly]);
axiom (forall<A> f : [LayerType]A, ly : LayerType :: { AtLayer(f,$LS(ly)) } AtLayer(f,$LS(ly)) == AtLayer(f,ly));

// ---------------------------------------------------------------
// -- Fields -----------------------------------------------------
// ---------------------------------------------------------------

type Field;

function FDim(Field): int;

function IndexField(int): Field;
axiom (forall i: int :: { IndexField(i) } FDim(IndexField(i)) == 1);
function IndexField_Inverse(Field): int;
axiom (forall i: int :: { IndexField(i) } IndexField_Inverse(IndexField(i)) == i);

function MultiIndexField(Field, int): Field;
axiom (forall f: Field, i: int :: { MultiIndexField(f,i) } FDim(MultiIndexField(f,i)) == FDim(f) + 1);
function MultiIndexField_Inverse0(Field): Field;
function MultiIndexField_Inverse1(Field): int;
axiom (forall f: Field, i: int :: { MultiIndexField(f,i) }
  MultiIndexField_Inverse0(MultiIndexField(f,i)) == f &&
  MultiIndexField_Inverse1(MultiIndexField(f,i)) == i);

function DeclType(Field): ClassName;

type NameFamily;
function DeclName(Field): NameFamily;
function FieldOfDecl(ClassName, NameFamily): Field;
axiom (forall cl : ClassName, nm: NameFamily ::
   {FieldOfDecl(cl, nm): Field}
   DeclType(FieldOfDecl(cl, nm): Field) == cl && DeclName(FieldOfDecl(cl, nm): Field) == nm);

function $IsGhostField(Field): bool;

// ---------------------------------------------------------------
// -- Allocatedness and Heap Succession --------------------------
// ---------------------------------------------------------------


// No heap-propagation axioms in qf-heap mode.

// ---------------------------------------------------------------
// -- Arrays -----------------------------------------------------
// ---------------------------------------------------------------

function _System.array.Length(a: ref): int;
axiom (forall o: ref :: {_System.array.Length(o)} 0 <= _System.array.Length(o));


// ---------------------------------------------------------------
// -- Reals ------------------------------------------------------
// ---------------------------------------------------------------

function Int(x: real): int { int(x) }
function {:inline} Real(x: int): real { real(x) }
axiom (forall i: int :: { Int(Real(i)) } Int(Real(i)) == i);

function {:inline} _System.real.Floor(x: real): int { Int(x) }

// ---------------------------------------------------------------
// -- The heap ---------------------------------------------------
// ---------------------------------------------------------------
type Heap = [ref][Field]Box;
function {:inline} read(H: Heap, r: ref, f: Field) : Box { H[r][f] }
function {:inline} update(H:Heap, r:ref, f: Field, v: Box) : Heap { H[r := H[r][f := v]] }
var $Alloc: [ref]bool;

function $IsGoodHeap(Heap): bool;
function $IsHeapAnchor(Heap): bool;
var $Heap: Heap;

// The following is used as a reference heap in places where the translation needs a heap
// but the expression generated is really one that is (at least in a correct program)
// independent of the heap.
const $OneHeap: Heap;

function $HeapSucc(Heap, Heap): bool;
function $HeapSuccGhost(Heap, Heap): bool;

// ---------------------------------------------------------------
// -- Useful macros ----------------------------------------------
// ---------------------------------------------------------------

// havoc everything in $Heap, except {this}+rds+nw
procedure $YieldHavoc(this: ref, rds: Set, nw: Set);
  modifies $Heap;

// havoc everything in $Heap, except rds-modi-{this}
procedure $IterHavoc0(this: ref, rds: Set, modi: Set);
  modifies $Heap;

// havoc $Heap at {this}+modi+nw
procedure $IterHavoc1(this: ref, modi: Set, nw: Set);
  modifies $Heap;

procedure $IterCollectNewObjects(prevHeap: Heap, newHeap: Heap, this: ref, NW: Field)
                        returns (s: Set);

// ---------------------------------------------------------------
// -- Axiomatizations --------------------------------------------
// ---------------------------------------------------------------

// ---------------------------------------------------------------
// -- Axiomatization of sets omitted in p3 -----------------------
// ---------------------------------------------------------------

type Set;

function Set#Card(s: Set) : int;
function Set#Empty() : Set;
function Set#IsMember(s: Set, o: Box) : bool;
function Set#UnionOne(s: Set, o: Box) : Set;
function Set#Union(a: Set, b: Set) : Set;
function Set#Intersection(a: Set, b: Set) : Set;
function Set#Difference(a: Set, b: Set) : Set;
function Set#Subset(a: Set, b: Set) : bool;
function Set#Equal(a: Set, b: Set) : bool;
function Set#Disjoint(a: Set, b: Set) : bool;
function Set#FromBoogieMap([Box]bool): Set;

// ---------------------------------------------------------------
// -- Axiomatization of isets omitted in p3 ----------------------
// ---------------------------------------------------------------

type ISet = [Box]bool;

function ISet#Empty(): ISet;
function ISet#FromSet(Set): ISet;
function ISet#UnionOne(ISet, Box): ISet;
function ISet#Union(ISet, ISet): ISet;
function ISet#Intersection(ISet, ISet): ISet;
function ISet#Difference(ISet, ISet): ISet;
function ISet#Subset(ISet, ISet): bool;
function ISet#Equal(ISet, ISet): bool;
function ISet#Disjoint(ISet, ISet): bool;

// ---------------------------------------------------------------
// -- Axiomatization of multisets omitted in p3 ------------------
// ---------------------------------------------------------------

function Math#min(a: int, b: int) : int;
function Math#clip(a: int) : int;

type MultiSet;

function MultiSet#Multiplicity(m: MultiSet, o: Box) : int;
function MultiSet#UpdateMultiplicity(m: MultiSet, o: Box, n: int) : MultiSet;
function $IsGoodMultiSet(ms: MultiSet) : bool;
function MultiSet#Card(m: MultiSet) : int;
function MultiSet#Empty() : MultiSet;
function MultiSet#Singleton(o: Box) : MultiSet;
function MultiSet#UnionOne(m: MultiSet, o: Box) : MultiSet;
function MultiSet#Union(a: MultiSet, b: MultiSet) : MultiSet;
function MultiSet#Intersection(a: MultiSet, b: MultiSet) : MultiSet;
function MultiSet#Difference(a: MultiSet, b: MultiSet) : MultiSet;
function MultiSet#Subset(a: MultiSet, b: MultiSet) : bool;
function MultiSet#Equal(a: MultiSet, b: MultiSet) : bool;
function MultiSet#Disjoint(a: MultiSet, b: MultiSet) : bool;
function MultiSet#FromSet(s: Set) : MultiSet;
function MultiSet#FromSeq(s: Seq) : MultiSet;

// ---------------------------------------------------------------
// -- Axiomatization of sequences omitted in p3 ------------------
// ---------------------------------------------------------------

type Seq;

function Seq#Length(s: Seq) : int;
function Seq#Empty() : Seq;
function Seq#Build(s: Seq, val: Box) : Seq;
function Seq#Build_inv0(s: Seq) : Seq;
function Seq#Build_inv1(s: Seq) : Box;
function Seq#Index(s: Seq, i: int) : Box;
function Seq#Update(s: Seq, i: int, val: Box) : Seq;
function Seq#Append(s0: Seq, s1: Seq) : Seq;
function Seq#Contains(s: Seq, val: Box) : bool;
function Seq#Equal(s0: Seq, s1: Seq) : bool;
function Seq#SameUntil(s0: Seq, s1: Seq, n: int) : bool;
function Seq#Take(s: Seq, howMany: int) : Seq;
function Seq#Drop(s: Seq, howMany: int) : Seq;
function Seq#Create(ty: Ty, heap: Heap, len: int, init: HandleType): Seq;
function Seq#FromArray(h: Heap, a: ref): Seq;
function Seq#Rank(Seq): int;

// ---------------------------------------------------------------
// -- Maps and IMaps omitted in p3 -------------------------------
// ---------------------------------------------------------------

type Map;
type IMap;

function #_System._tuple#2._#Make2(Box, Box) : DatatypeType;
function _System.Tuple2._0(DatatypeType) : Box;
function _System.Tuple2._1(DatatypeType) : Box;

function Map#Domain(Map) : Set;
function Map#Elements(Map) : [Box]Box;
function Map#Card(Map) : int;
function Map#Values(Map) : Set;
function Map#Items(Map) : Set;
function Map#Empty() : Map;
function Map#Glue(Set, [Box]Box, Ty) : Map;
function Map#Build(Map, Box, Box) : Map;
function Map#Merge(Map, Map) : Map;
function Map#Subtract(Map, Set) : Map;
function Map#Equal(Map, Map) : bool;
function Map#Disjoint(Map, Map) : bool;

function IMap#Domain(IMap) : ISet;
function IMap#Elements(IMap) : [Box]Box;
function IMap#Values(IMap) : ISet;
function IMap#Items(IMap) : ISet;
function IMap#Empty() : IMap;
function IMap#Glue([Box]bool, [Box]Box, Ty) : IMap;
function IMap#Build(IMap, Box, Box) : IMap;
function IMap#Equal(IMap, IMap) : bool;
function IMap#Merge(IMap, IMap) : IMap;
function IMap#Subtract(IMap, Set) : IMap;

// -------------------------------------------------------------------------
// -- Provide arithmetic wrappers to improve triggering and non-linear math
// -------------------------------------------------------------------------

function INTERNAL_add_boogie(x:int, y:int) : int { x + y }
function INTERNAL_sub_boogie(x:int, y:int) : int { x - y }
function INTERNAL_mul_boogie(x:int, y:int) : int { x * y }
function INTERNAL_div_boogie(x:int, y:int) : int { x div y }
function INTERNAL_mod_boogie(x:int, y:int) : int { x mod y }
function {:never_pattern true} INTERNAL_lt_boogie(x:int, y:int) : bool { x < y }
function {:never_pattern true} INTERNAL_le_boogie(x:int, y:int) : bool { x <= y }
function {:never_pattern true} INTERNAL_gt_boogie(x:int, y:int) : bool { x > y }
function {:never_pattern true} INTERNAL_ge_boogie(x:int, y:int) : bool { x >= y }

function Mul(x, y: int): int { x * y }
function Div(x, y: int): int { x div y }
function Mod(x, y: int): int { x mod y }
function Add(x, y: int): int { x + y }
function Sub(x, y: int): int { x - y }

#if ARITH_DISTR
axiom (forall x, y, z: int ::
  { Mul(Add(x, y), z) }
  Mul(Add(x, y), z) == Add(Mul(x, z), Mul(y, z)));
axiom (forall x,y,z: int ::
  { Mul(x, Add(y, z)) }
  Mul(x, Add(y, z)) == Add(Mul(x, y), Mul(x, z)));
//axiom (forall x, y, z: int ::
//  { Mul(Sub(x, y), z) }
//  Mul(Sub(x, y), z) == Sub(Mul(x, z), Mul(y, z)));
#endif
#if ARITH_MUL_DIV_MOD
axiom (forall x, y: int ::
  { Div(x, y), Mod(x, y) }
  { Mul(Div(x, y), y) }
  y != 0 ==>
  Mul(Div(x, y), y) + Mod(x, y) == x);
#endif
#if ARITH_MUL_SIGN
axiom (forall x, y: int ::
  { Mul(x, y) }
  ((0 <= x && 0 <= y) || (x <= 0 && y <= 0) ==> 0 <= Mul(x, y)));
#endif
#if ARITH_MUL_COMM
axiom (forall x, y: int ::
  { Mul(x, y) }
  Mul(x, y) == Mul(y, x));
#endif
#if ARITH_MUL_ASSOC
axiom (forall x, y, z: int ::
  { Mul(x, Mul(y, z)) }
  Mul(y, z) != z && Mul(y, z) != y ==> Mul(x, Mul(y, z)) == Mul(Mul(x, y), z));
#endif

// -------------------------------------------------------------------------
