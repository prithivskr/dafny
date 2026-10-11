
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

revealed function {:identity} LitInt(x: int) : int;

revealed function {:identity} LitReal(x: real) : real;

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

revealed function local_field(ff: FieldFamily, depth: int) : Field;

type Box;

const $ArbitraryBoxValue: Box;

revealed function $IsBox(Box, Ty) : bool;

revealed function $IsAllocBox(Box, Ty, [ref][Field]Box) : bool;

revealed function $AlwaysAllocated(Ty) : bool;

revealed function $OlderTag([ref][Field]Box) : bool;

type ClassName;

const unique class._System.int: ClassName;

const unique class._System.bool: ClassName;

const unique class._System.set: ClassName;

const unique class._System.seq: ClassName;

const unique class._System.multiset: ClassName;

revealed function Tclass._System.object?() : Ty
uses {
// Tclass._System.object? Tag
axiom TagFamily(Tclass._System.object?()) == tytagFamily$object;
// Tclass._System.object? Tag
axiom Tag(Tclass._System.object?()) == Tagclass._System.object?;
}

revealed function Tclass._System.Tuple2(Ty, Ty) : Ty;

revealed function dtype(ref) : Ty;

revealed function TypeTuple(a: ClassName, b: ClassName) : ClassName;

revealed function TypeTupleCar(ClassName) : ClassName;

revealed function TypeTupleCdr(ClassName) : ClassName;

type HandleType;

revealed function SetRef_to_SetBox(s: [ref]bool) : [Box]bool;

revealed function Apply1(Ty, Ty, [ref][Field]Box, HandleType, Box) : Box;

revealed function Requires0(Ty, [ref][Field]Box, HandleType) : bool;

revealed function Requires1(Ty, Ty, [ref][Field]Box, HandleType, Box) : bool;

revealed function Requires2(Ty, Ty, Ty, [ref][Field]Box, HandleType, Box, Box) : bool;

revealed function Reads0(Ty, [ref][Field]Box, HandleType) : [Box]bool;

revealed function Reads1(Ty, Ty, [ref][Field]Box, HandleType, Box) : [Box]bool;

revealed function Reads2(Ty, Ty, Ty, [ref][Field]Box, HandleType, Box, Box) : [Box]bool;

revealed function Requires0#canCall(Ty, [ref][Field]Box, HandleType) : bool;

revealed function Requires1#canCall(Ty, Ty, [ref][Field]Box, HandleType, Box) : bool;

revealed function Requires2#canCall(Ty, Ty, Ty, [ref][Field]Box, HandleType, Box, Box) : bool;

type DatatypeType;

type DtCtorId;

revealed function DatatypeCtorId(DatatypeType) : DtCtorId;

revealed function DtRank(DatatypeType) : int;

revealed function BoxRank(Box) : int;

type ORDINAL = Box;

revealed function ORD#IsNat(Box) : bool;

revealed function ORD#Offset(Box) : int;

revealed function {:inline} ORD#IsLimit(o: Box) : bool
{
  ORD#Offset(o) == 0
}

revealed function {:inline} ORD#IsSucc(o: Box) : bool
{
  0 < ORD#Offset(o)
}

revealed function ORD#FromNat(int) : Box;

revealed function ORD#Less(Box, Box) : bool;

revealed function ORD#LessThanLimit(Box, Box) : bool;

revealed function ORD#Plus(Box, Box) : Box;

revealed function ORD#Minus(Box, Box) : Box;

type LayerType;

const $LZ: LayerType;

revealed function $LS(LayerType) : LayerType;

revealed function AsFuelBottom(LayerType) : LayerType;

type Field;

revealed function FDim(Field) : int;

revealed function IndexField(int) : Field;

revealed function IndexField_Inverse(Field) : int;

revealed function MultiIndexField(Field, int) : Field;

revealed function MultiIndexField_Inverse0(Field) : Field;

revealed function MultiIndexField_Inverse1(Field) : int;

revealed function DeclType(Field) : ClassName;

type NameFamily;

revealed function DeclName(Field) : NameFamily;

revealed function FieldOfDecl(ClassName, NameFamily) : Field;

revealed function $IsGhostField(Field) : bool;

revealed function {:inline} _System.array.Length(a: ref) : int
{
  0
}

revealed function Int(x: real) : int;

revealed function {:inline} Real(x: int) : real
{
  real(x)
}

revealed function {:inline} _System.real.Floor(x: real) : int
{
  Int(x)
}

type Heap = [ref][Field]Box;

revealed function {:inline} read(H: [ref][Field]Box, r: ref, f: Field) : Box
{
  H[r][f]
}

revealed function {:inline} update(H: [ref][Field]Box, r: ref, f: Field, v: Box) : [ref][Field]Box
{
  H[r := H[r][f := v]]
}

var $Alloc: [Box]bool;

revealed function $IsGoodHeap([ref][Field]Box) : bool;

revealed function $IsHeapAnchor([ref][Field]Box) : bool;

var $Heap: [ref][Field]Box;

const $OneHeap: [ref][Field]Box;

revealed function $HeapSucc([ref][Field]Box, [ref][Field]Box) : bool;

revealed function $HeapSuccGhost([ref][Field]Box, [ref][Field]Box) : bool;

procedure $YieldHavoc(this: ref, rds: [Box]bool, nw: [Box]bool);
  modifies $Heap;



procedure $IterHavoc0(this: ref, rds: [Box]bool, modi: [Box]bool);
  modifies $Heap;



procedure $IterHavoc1(this: ref, modi: [Box]bool, nw: [Box]bool);
  modifies $Heap;



procedure $IterCollectNewObjects(prevHeap: [ref][Field]Box, newHeap: [ref][Field]Box, this: ref, NW: Field)
   returns (s: [Box]bool);



type Set = [Box]bool;

revealed function {:inline} Set#IsMember(s: [Box]bool, o: Box) : bool
{
  s[o]
}

revealed function {:inline} Set#Empty() : [Box]bool
{
  $QfSetConst(false)
}

revealed function {:inline} Set#UnionOne(s: [Box]bool, x: Box) : [Box]bool
{
  s[x := true]
}

revealed function {:builtin "MapOr"} Set#Union(a: [Box]bool, b: [Box]bool) : [Box]bool;

revealed function {:builtin "MapAnd"} Set#Intersection(a: [Box]bool, b: [Box]bool) : [Box]bool;

revealed function {:inline} Set#Difference(a: [Box]bool, b: [Box]bool) : [Box]bool
{
  Set#Intersection(a, $QfSetNot(b))
}

revealed function {:inline} Set#Equal(a: [Box]bool, b: [Box]bool) : bool
{
  a == b
}

revealed function {:inline} Set#Subset(a: [Box]bool, b: [Box]bool) : bool
{
  Set#Equal(Set#Difference(a, b), Set#Empty())
}

revealed function {:inline} Set#Disjoint(a: [Box]bool, b: [Box]bool) : bool
{
  Set#Equal(Set#Intersection(a, b), Set#Empty())
}

revealed function {:inline} Set#FromBoogieMap(m: [Box]bool) : [Box]bool
{
  m
}

revealed function Set#Card(s: [Box]bool) : int;

type ISet = [Box]bool;

revealed function ISet#Empty() : [Box]bool;

revealed function ISet#FromSet([Box]bool) : [Box]bool;

revealed function ISet#UnionOne([Box]bool, Box) : [Box]bool;

revealed function ISet#Union([Box]bool, [Box]bool) : [Box]bool;

revealed function ISet#Intersection([Box]bool, [Box]bool) : [Box]bool;

revealed function ISet#Difference([Box]bool, [Box]bool) : [Box]bool;

revealed function ISet#Subset([Box]bool, [Box]bool) : bool;

revealed function ISet#Equal([Box]bool, [Box]bool) : bool;

revealed function ISet#Disjoint([Box]bool, [Box]bool) : bool;

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

revealed function MultiSet#FromSet(s: [Box]bool) : MultiSet;

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

revealed function Seq#Create(ty: Ty, heap: [ref][Field]Box, len: int, init: HandleType) : Seq;

revealed function Seq#FromArray(h: [ref][Field]Box, a: ref) : Seq;

revealed function Seq#Rank(Seq) : int;

type Map;

type IMap;

revealed function #_System._tuple#2._#Make2(Box, Box) : DatatypeType;

revealed function _System.Tuple2._0(DatatypeType) : Box;

revealed function _System.Tuple2._1(DatatypeType) : Box;

revealed function Map#Domain(Map) : [Box]bool;

revealed function Map#Elements(Map) : [Box]Box;

revealed function Map#Card(Map) : int;

revealed function Map#Values(Map) : [Box]bool;

revealed function Map#Items(Map) : [Box]bool;

revealed function Map#Empty() : Map;

revealed function Map#Glue([Box]bool, [Box]Box, Ty) : Map;

revealed function Map#Build(Map, Box, Box) : Map;

revealed function Map#Merge(Map, Map) : Map;

revealed function Map#Subtract(Map, [Box]bool) : Map;

revealed function Map#Equal(Map, Map) : bool;

revealed function Map#Disjoint(Map, Map) : bool;

revealed function IMap#Domain(IMap) : [Box]bool;

revealed function IMap#Elements(IMap) : [Box]Box;

revealed function IMap#Values(IMap) : [Box]bool;

revealed function IMap#Items(IMap) : [Box]bool;

revealed function IMap#Empty() : IMap;

revealed function IMap#Glue([Box]bool, [Box]Box, Ty) : IMap;

revealed function IMap#Build(IMap, Box, Box) : IMap;

revealed function IMap#Equal(IMap, IMap) : bool;

revealed function IMap#Merge(IMap, IMap) : IMap;

revealed function IMap#Subtract(IMap, [Box]bool) : IMap;

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

revealed function {:builtin "MapConst"} $QfSetConst(a: bool) : [Box]bool;

revealed function {:builtin "MapNot"} $QfSetNot(a: [Box]bool) : [Box]bool;

function Tclass._System.nat() : Ty
uses {
// Tclass._System.nat Tag
axiom TagFamily(Tclass._System.nat()) == tytagFamily$nat;
// Tclass._System.nat Tag
axiom Tag(Tclass._System.nat()) == Tagclass._System.nat;
}

const unique Tagclass._System.nat: TyTag;

const unique class._System.object?: ClassName;

const unique Tagclass._System.object?: TyTag;

function implements$_System.object(ty: Ty) : bool;

function Tclass._System.object() : Ty
uses {
// Tclass._System.object Tag
axiom TagFamily(Tclass._System.object()) == tytagFamily$object;
// Tclass._System.object Tag
axiom Tag(Tclass._System.object()) == Tagclass._System.object;
}

const unique Tagclass._System.object: TyTag;

const unique class._System.array?: ClassName;

function Tclass._System.array?(Ty) : Ty;

const unique Tagclass._System.array?: TyTag;

function Tclass._System.array?_0(Ty) : Ty;

function Tclass._System.array(Ty) : Ty;

const unique Tagclass._System.array: TyTag;

function Tclass._System.array_0(Ty) : Ty;

function Tclass._System.___hFunc1(Ty, Ty) : Ty;

const unique Tagclass._System.___hFunc1: TyTag;

function Tclass._System.___hFunc1_0(Ty) : Ty;

function Tclass._System.___hFunc1_1(Ty) : Ty;

function Tclass._System.___hPartialFunc1(Ty, Ty) : Ty;

const unique Tagclass._System.___hPartialFunc1: TyTag;

function Tclass._System.___hPartialFunc1_0(Ty) : Ty;

function Tclass._System.___hPartialFunc1_1(Ty) : Ty;

function Tclass._System.___hTotalFunc1(Ty, Ty) : Ty;

const unique Tagclass._System.___hTotalFunc1: TyTag;

function Tclass._System.___hTotalFunc1_0(Ty) : Ty;

function Tclass._System.___hTotalFunc1_1(Ty) : Ty;

function Tclass._System.___hFunc0(Ty) : Ty;

const unique Tagclass._System.___hFunc0: TyTag;

function Tclass._System.___hFunc0_0(Ty) : Ty;

function Tclass._System.___hPartialFunc0(Ty) : Ty;

const unique Tagclass._System.___hPartialFunc0: TyTag;

function Tclass._System.___hPartialFunc0_0(Ty) : Ty;

function Tclass._System.___hTotalFunc0(Ty) : Ty;

const unique Tagclass._System.___hTotalFunc0: TyTag;

function Tclass._System.___hTotalFunc0_0(Ty) : Ty;

const unique ##_System._tuple#2._#Make2: DtCtorId;

function _System.Tuple2.___hMake2_q(DatatypeType) : bool;

const unique Tagclass._System.Tuple2: TyTag;

function Tclass._System.Tuple2_0(Ty) : Ty;

function Tclass._System.Tuple2_1(Ty) : Ty;

// Depth-one case-split function
function $IsA#_System.Tuple2(DatatypeType) : bool;

// Datatype extensional equality declaration
function _System.Tuple2#Equal(DatatypeType, DatatypeType) : bool;

const unique class._System.Tuple2: ClassName;

// Constructor function declaration
function #_System._tuple#0._#Make0() : DatatypeType
uses {
// Constructor identifier
axiom DatatypeCtorId(#_System._tuple#0._#Make0()) == ##_System._tuple#0._#Make0;
// Constructor $Is
axiom $Is_11119(#_System._tuple#0._#Make0(), Tclass._System.Tuple0());
// Constructor literal
axiom #_System._tuple#0._#Make0() == Lit_11119(#_System._tuple#0._#Make0());
}

const unique ##_System._tuple#0._#Make0: DtCtorId
uses {
// Constructor identifier
axiom DatatypeCtorId(#_System._tuple#0._#Make0()) == ##_System._tuple#0._#Make0;
}

function _System.Tuple0.___hMake0_q(DatatypeType) : bool;

function Tclass._System.Tuple0() : Ty
uses {
// Tclass._System.Tuple0 Tag
axiom TagFamily(Tclass._System.Tuple0()) == tytagFamily$_tuple#0;
// Tclass._System.Tuple0 Tag
axiom Tag(Tclass._System.Tuple0()) == Tagclass._System.Tuple0;
}

const unique Tagclass._System.Tuple0: TyTag;

// Depth-one case-split function
function $IsA#_System.Tuple0(DatatypeType) : bool;

// Datatype extensional equality declaration
function _System.Tuple0#Equal(DatatypeType, DatatypeType) : bool;

const unique class._System.Tuple0: ClassName;

function Tclass._System.___hFunc2(Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hFunc2: TyTag;

function Tclass._System.___hFunc2_0(Ty) : Ty;

function Tclass._System.___hFunc2_1(Ty) : Ty;

function Tclass._System.___hFunc2_2(Ty) : Ty;

function Tclass._System.___hPartialFunc2(Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hPartialFunc2: TyTag;

function Tclass._System.___hPartialFunc2_0(Ty) : Ty;

function Tclass._System.___hPartialFunc2_1(Ty) : Ty;

function Tclass._System.___hPartialFunc2_2(Ty) : Ty;

function Tclass._System.___hTotalFunc2(Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hTotalFunc2: TyTag;

function Tclass._System.___hTotalFunc2_0(Ty) : Ty;

function Tclass._System.___hTotalFunc2_1(Ty) : Ty;

function Tclass._System.___hTotalFunc2_2(Ty) : Ty;

const reveal__module._default.Observe: bool;

const unique class._module.__default: ClassName;

// function declaration for _module._default.Observe
function _module.__default.Observe($reveal: bool, $heap: [ref][Field]Box, x#0: ref) : int;

function _module.__default.Observe#canCall($heap: [ref][Field]Box, x#0: ref) : bool;

function Tclass._module.Cell() : Ty
uses {
// Tclass._module.Cell Tag
axiom TagFamily(Tclass._module.Cell()) == tytagFamily$Cell;
// Tclass._module.Cell Tag
axiom Tag(Tclass._module.Cell()) == Tagclass._module.Cell;
}

const unique Tagclass._module.Cell: TyTag;

function _module.__default.Observe#requires([ref][Field]Box, ref) : bool;

procedure {:verboseName "Observe (well-formedness)"} CheckWellformed$$_module.__default.Observe(x#0: ref
       where ($Is_11208(x#0, Tclass._module.Cell())
           <==> $Is_11208(x#0, Tclass._module.Cell?()) && x#0 != null)
         && ($Is_11208(x#0, Tclass._module.Cell?())
           <==> x#0 == null || dtype(x#0) == Tclass._module.Cell?())
         && $Is_11208(x#0, Tclass._module.Cell()));
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Observe (well-formedness)"} CheckWellformed$$_module.__default.Observe(x#0: ref)
{
  var $qfFrameSet#0: [Box]bool;
  var $qfFrameAlloc#0: [Box]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

  anon0:
    b$reqreads#0 := true;
    b$reqreads#1 := true;
    assume true;
    goto anon1;

  anon1:
    assume {:captureState "example.dfy(6,25): initial state"} true;
    assume $Unbox_11205($Box_11205(x#0)) == x#0
       && $Box_15550($Unbox_15532(read($Heap, x#0, _module.Cell.fp)))
         == read($Heap, x#0, _module.Cell.fp)
       && $Unbox_11205($Box_11205(null)) == null;
    $qfFrameSet#0 := Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
        $Unbox_15532(read($Heap, x#0, _module.Cell.fp))), 
      Set#UnionOne(Set#Empty(), $Box_11205(null)));
    $qfFrameAlloc#0 := $Alloc;
    // Check well-formedness of preconditions, and then assume them
    // Check well-formedness of the reads clause
    assume $Unbox_11205($Box_11205(x#0)) == x#0;
    assume 0 <= Set#Card(Set#UnionOne(Set#Empty(), $Box_11205(x#0)));
    assume Set#Card(Set#UnionOne(Set#Empty(), $Box_11205(x#0))) == 0
       <==> Set#Equal(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), Set#Empty());
    assume Set#Card(Set#Empty()) == 0;
    assume Set#Card(Set#UnionOne(Set#Empty(), $Box_11205(x#0)))
       == Set#Card(Set#Empty())
         + (if Set#IsMember(Set#Empty(), $Box_11205(x#0)) then 0 else 1);
    assert {:id "id1"} x#0 != null;
    b$reqreads#0 := !(x#0 != null && $qfFrameAlloc#0[$Box_11205(x#0)])
       || Set#IsMember($qfFrameSet#0, $Box_11205(x#0));
    assume $Box_15550($Unbox_15532(read($Heap, x#0, _module.Cell.fp)))
         == read($Heap, x#0, _module.Cell.fp)
       && Inv0_TSet(TSet(Tclass._module.Cell())) == Tclass._module.Cell()
       && Tag(TSet(Tclass._module.Cell())) == TagSet;
    assume $Is_15593($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), TSet(Tclass._module.Cell()));
    assume true;
    assume 0 <= Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp)));
    assume Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp))) == 0
       <==> Set#Equal($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), Set#Empty());
    assume 0 <= Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp)));
    assume Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp))) == 0
       <==> Set#Equal($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), Set#Empty());
    assume $Unbox_11205($Box_11205(x#0)) == x#0;
    assume 0
       <= Set#Card(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
          $Unbox_15532(read($Heap, x#0, _module.Cell.fp))));
    assume Set#Card(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
            $Unbox_15532(read($Heap, x#0, _module.Cell.fp))))
         == 0
       <==> Set#Equal(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
          $Unbox_15532(read($Heap, x#0, _module.Cell.fp))), 
        Set#Empty());
    assume 0 <= Set#Card(Set#UnionOne(Set#Empty(), $Box_11205(x#0)));
    assume Set#Card(Set#UnionOne(Set#Empty(), $Box_11205(x#0))) == 0
       <==> Set#Equal(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), Set#Empty());
    assume 0 <= Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp)));
    assume Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp))) == 0
       <==> Set#Equal($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), Set#Empty());
    assume 0
       <= Set#Card(Set#Intersection(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
          $Unbox_15532(read($Heap, x#0, _module.Cell.fp))));
    assume Set#Card(Set#Intersection(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
            $Unbox_15532(read($Heap, x#0, _module.Cell.fp))))
         == 0
       <==> Set#Equal(Set#Intersection(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
          $Unbox_15532(read($Heap, x#0, _module.Cell.fp))), 
        Set#Empty());
    assume Set#Card(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
            $Unbox_15532(read($Heap, x#0, _module.Cell.fp))))
         + Set#Card(Set#Intersection(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
            $Unbox_15532(read($Heap, x#0, _module.Cell.fp))))
       == Set#Card(Set#UnionOne(Set#Empty(), $Box_11205(x#0)))
         + Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp)));
    assert {:id "id2"} b$reqreads#0;
    // Check well-formedness of the decreases clause
    assume 0 <= Set#Card(Set#UnionOne(Set#Empty(), $Box_11205(x#0)));
    assume Set#Card(Set#UnionOne(Set#Empty(), $Box_11205(x#0))) == 0
       <==> Set#Equal(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), Set#Empty());
    assume Set#Card(Set#Empty()) == 0;
    assume Set#Card(Set#UnionOne(Set#Empty(), $Box_11205(x#0)))
       == Set#Card(Set#Empty())
         + (if Set#IsMember(Set#Empty(), $Box_11205(x#0)) then 0 else 1);
    assert {:id "id3"} x#0 != null;
    assume $Is_15593($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), TSet(Tclass._module.Cell()));
    assume true;
    assume 0 <= Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp)));
    assume Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp))) == 0
       <==> Set#Equal($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), Set#Empty());
    assume 0 <= Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp)));
    assume Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp))) == 0
       <==> Set#Equal($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), Set#Empty());
    assume 0
       <= Set#Card(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
          $Unbox_15532(read($Heap, x#0, _module.Cell.fp))));
    assume Set#Card(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
            $Unbox_15532(read($Heap, x#0, _module.Cell.fp))))
         == 0
       <==> Set#Equal(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
          $Unbox_15532(read($Heap, x#0, _module.Cell.fp))), 
        Set#Empty());
    assume 0 <= Set#Card(Set#UnionOne(Set#Empty(), $Box_11205(x#0)));
    assume Set#Card(Set#UnionOne(Set#Empty(), $Box_11205(x#0))) == 0
       <==> Set#Equal(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), Set#Empty());
    assume 0 <= Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp)));
    assume Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp))) == 0
       <==> Set#Equal($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), Set#Empty());
    assume 0
       <= Set#Card(Set#Intersection(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
          $Unbox_15532(read($Heap, x#0, _module.Cell.fp))));
    assume Set#Card(Set#Intersection(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
            $Unbox_15532(read($Heap, x#0, _module.Cell.fp))))
         == 0
       <==> Set#Equal(Set#Intersection(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
          $Unbox_15532(read($Heap, x#0, _module.Cell.fp))), 
        Set#Empty());
    assume Set#Card(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
            $Unbox_15532(read($Heap, x#0, _module.Cell.fp))))
         + Set#Card(Set#Intersection(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
            $Unbox_15532(read($Heap, x#0, _module.Cell.fp))))
       == Set#Card(Set#UnionOne(Set#Empty(), $Box_11205(x#0)))
         + Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp)));
    assume 0
       <= Set#Card(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
          $Unbox_15532(read($Heap, x#0, _module.Cell.fp))));
    assume Set#Card(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
            $Unbox_15532(read($Heap, x#0, _module.Cell.fp))))
         == 0
       <==> Set#Equal(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
          $Unbox_15532(read($Heap, x#0, _module.Cell.fp))), 
        Set#Empty());
    // Check body and ensures clauses
    assume true;
    goto anon5_Then, anon5_Else;

  anon5_Then:
    // Check well-formedness of postcondition and assume false
    assume false;
    assume true;
    return;

  anon5_Else:
    // Check well-formedness of body and result subset type constraint
    assert {:id "id4"} x#0 != null;
    assume $Unbox_11205($Box_11205(x#0)) == x#0;
    b$reqreads#1 := !(x#0 != null && $qfFrameAlloc#0[$Box_11205(x#0)])
       || Set#IsMember($qfFrameSet#0, $Box_11205(x#0));
    assume true;
    assume true;
    assume $Box_331($Unbox_637(read($Heap, x#0, _module.Cell.value)))
         == read($Heap, x#0, _module.Cell.value)
       && ($IsGoodHeap($Heap) && $Is_11208(x#0, Tclass._module.Cell())
         ==> (_module.__default.Observe#requires($Heap, x#0) <==> true))
       && (_module.__default.Observe#requires($Heap, x#0)
         ==> _module.__default.Observe#canCall($Heap, x#0))
       && ($Is_11208(x#0, Tclass._module.Cell())
         <==> $Is_11208(x#0, Tclass._module.Cell?()) && x#0 != null)
       && ($Is_11208(x#0, Tclass._module.Cell?())
         <==> x#0 == null || dtype(x#0) == Tclass._module.Cell?());
    assume {:id "id5"} _module.__default.Observe(reveal__module._default.Observe, $Heap, x#0)
       == $Unbox_637(read($Heap, x#0, _module.Cell.value));
    // CheckWellformedWithResult: any expression
    assume $Is_2(_module.__default.Observe(reveal__module._default.Observe, $Heap, x#0), TInt);
    assert {:id "id6"} b$reqreads#1;
    assume true;
    return;

  anon4:
    assume false;
    assume true;
    return;
}



procedure {:verboseName "Change (well-formedness)"} CheckWellFormed$$_module.__default.Change(y#0: ref
       where ($Is_11208(y#0, Tclass._module.Cell())
           <==> $Is_11208(y#0, Tclass._module.Cell?()) && y#0 != null)
         && $Unbox_11205($Box_11205(y#0)) == y#0
         && ($Is_11208(y#0, Tclass._module.Cell?())
           <==> y#0 == null || dtype(y#0) == Tclass._module.Cell?())
         && 
        $Is_11208(y#0, Tclass._module.Cell())
         && (y#0 == null || $Alloc[$Box_11205(y#0)]));
  modifies $Heap, $Alloc;



procedure {:verboseName "Change (call)"} Call$$_module.__default.Change(y#0: ref
       where ($Is_11208(y#0, Tclass._module.Cell())
           <==> $Is_11208(y#0, Tclass._module.Cell?()) && y#0 != null)
         && $Unbox_11205($Box_11205(y#0)) == y#0
         && ($Is_11208(y#0, Tclass._module.Cell?())
           <==> y#0 == null || dtype(y#0) == Tclass._module.Cell?())
         && 
        $Is_11208(y#0, Tclass._module.Cell())
         && (y#0 == null || $Alloc[$Box_11205(y#0)]));
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires true;
  modifies $Heap, $Alloc;



procedure {:verboseName "Change (correctness)"} Impl$$_module.__default.Change(y#0: ref
       where ($Is_11208(y#0, Tclass._module.Cell())
           <==> $Is_11208(y#0, Tclass._module.Cell?()) && y#0 != null)
         && $Unbox_11205($Box_11205(y#0)) == y#0
         && ($Is_11208(y#0, Tclass._module.Cell?())
           <==> y#0 == null || dtype(y#0) == Tclass._module.Cell?())
         && 
        $Is_11208(y#0, Tclass._module.Cell())
         && (y#0 == null || $Alloc[$Box_11205(y#0)]))
   returns ($_reverifyPost: bool);
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires true;
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Change (correctness)"} Impl$$_module.__default.Change(y#0: ref) returns ($_reverifyPost: bool)
{
  var $qfFrameSet#1: [Box]bool;
  var $qfFrameAlloc#1: [Box]bool;
  var $rhs#0: int;
  var $PreWriteHeap#0: [ref][Field]Box;
  var $PreWriteAlloc#0: [Box]bool;
  var $qfWrittenObject: ref;

  anon0:
    // AddMethodImpl: Change, Impl$$_module.__default.Change
    assume $Unbox_11205($Box_11205(y#0)) == y#0 && $Unbox_11205($Box_11205(null)) == null;
    $qfFrameSet#1 := Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
      Set#UnionOne(Set#Empty(), $Box_11205(null)));
    $qfFrameAlloc#1 := $Alloc;
    assume {:captureState "example.dfy(14,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/example.dfy(15,11)
    assert {:id "id7"} y#0 != null;
    assume true;
    assume true;
    assume $Unbox_11205($Box_11205(y#0)) == y#0;
    assert {:id "id8"} !(y#0 != null && $qfFrameAlloc#1[$Box_11205(y#0)])
       || Set#IsMember($qfFrameSet#1, $Box_11205(y#0));
    assert {:id "id9"} y#0 != null;
    assume true;
    assume true;
    assume $Box_331($Unbox_637(read($Heap, y#0, _module.Cell.value)))
       == read($Heap, y#0, _module.Cell.value);
    $rhs#0 := $Unbox_637(read($Heap, y#0, _module.Cell.value)) + 1;
    $PreWriteHeap#0 := $Heap;
    $PreWriteAlloc#0 := $Alloc;
    $qfWrittenObject := y#0;
    assume $Unbox_637($Box_331($rhs#0)) == $rhs#0;
    $Heap := update($Heap, y#0, _module.Cell.value, $Box_331($rhs#0));
    assume true;
    // qf-mutation-frame: full reads supports
    assume $PreWriteAlloc#0 == $Alloc;
    assume $Unbox_11205($Box_11205($qfWrittenObject)) == $qfWrittenObject
       && $Unbox_11205($Box_11205(y#0)) == y#0;
    assume y#0 != null
         && !
        (Set#IsMember(Set#UnionOne(Set#Empty(), $Box_11205($qfWrittenObject)), $Box_11205(y#0))
         && _module.Cell.value == _module.Cell.value)
       ==> read($PreWriteHeap#0, y#0, _module.Cell.value)
         == read($Heap, y#0, _module.Cell.value);
    assume {:captureState "example.dfy(15,24)"} true;
    assume true;
    return;
}



procedure {:verboseName "Test (well-formedness)"} CheckWellFormed$$_module.__default.Test(x#0: ref
       where ($Is_11208(x#0, Tclass._module.Cell())
           <==> $Is_11208(x#0, Tclass._module.Cell?()) && x#0 != null)
         && $Unbox_11205($Box_11205(x#0)) == x#0
         && ($Is_11208(x#0, Tclass._module.Cell?())
           <==> x#0 == null || dtype(x#0) == Tclass._module.Cell?())
         && 
        $Is_11208(x#0, Tclass._module.Cell())
         && (x#0 == null || $Alloc[$Box_11205(x#0)]), 
    y#0: ref
       where ($Is_11208(y#0, Tclass._module.Cell())
           <==> $Is_11208(y#0, Tclass._module.Cell?()) && y#0 != null)
         && $Unbox_11205($Box_11205(y#0)) == y#0
         && ($Is_11208(y#0, Tclass._module.Cell?())
           <==> y#0 == null || dtype(y#0) == Tclass._module.Cell?())
         && 
        $Is_11208(y#0, Tclass._module.Cell())
         && (y#0 == null || $Alloc[$Box_11205(y#0)]));
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Test (well-formedness)"} CheckWellFormed$$_module.__default.Test(x#0: ref, y#0: ref)
{
  var $qfFrameSet#0: [Box]bool;
  var $qfFrameAlloc#0: [Box]bool;

  anon0:
    assume true;
    goto anon1;

  anon1:
    // AddMethodImpl: Test, CheckWellFormed$$_module.__default.Test
    assume $Unbox_11205($Box_11205(y#0)) == y#0 && $Unbox_11205($Box_11205(null)) == null;
    $qfFrameSet#0 := Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
      Set#UnionOne(Set#Empty(), $Box_11205(null)));
    $qfFrameAlloc#0 := $Alloc;
    assume {:captureState "example.dfy(18,7): initial state"} true;
    assume {:id "id12"} x#0 != y#0;
    assert {:id "id13"} x#0 != null;
    assume $Box_15550($Unbox_15532(read($Heap, x#0, _module.Cell.fp)))
         == read($Heap, x#0, _module.Cell.fp)
       && Inv0_TSet(TSet(Tclass._module.Cell())) == Tclass._module.Cell()
       && Tag(TSet(Tclass._module.Cell())) == TagSet;
    assume $Is_15593($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), TSet(Tclass._module.Cell()));
    assume true;
    assume 0 <= Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp)));
    assume Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp))) == 0
       <==> Set#Equal($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), Set#Empty());
    assume 0 <= Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp)));
    assume Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp))) == 0
       <==> Set#Equal($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), Set#Empty());
    assume $Unbox_11205($Box_11205(y#0)) == y#0;
    assume {:id "id14"} !Set#IsMember($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), $Box_11205(y#0));
    havoc $Heap, $Alloc;
    assume Set#Equal(Set#Difference(old($Alloc), $Alloc), Set#Empty());
    assume $Box_15550($Unbox_15532(read(old($Heap), x#0, _module.Cell.fp)))
         == read(old($Heap), x#0, _module.Cell.fp)
       && Inv0_TSet(TSet(Tclass._module.Cell())) == Tclass._module.Cell()
       && Tag(TSet(Tclass._module.Cell())) == TagSet
       && $Unbox_11205($Box_11205(x#0)) == x#0
       && ($Is_11208(x#0, Tclass._module.Cell())
         <==> $Is_11208(x#0, Tclass._module.Cell?()) && x#0 != null)
       && ($Is_11208(x#0, Tclass._module.Cell?())
         <==> x#0 == null || dtype(x#0) == Tclass._module.Cell?());
    assume $Is_15593($Unbox_15532(read(old($Heap), x#0, _module.Cell.fp)), 
          TSet(Tclass._module.Cell()))
         && Set#IsMember($Unbox_15532(read(old($Heap), x#0, _module.Cell.fp)), $Box_11205(x#0))
       ==> $Is_11208(x#0, Tclass._module.Cell());
    assume $Unbox_11205($Box_11205(y#0)) == y#0
       && ($Is_11208(y#0, Tclass._module.Cell())
         <==> $Is_11208(y#0, Tclass._module.Cell?()) && y#0 != null)
       && ($Is_11208(y#0, Tclass._module.Cell?())
         <==> y#0 == null || dtype(y#0) == Tclass._module.Cell?());
    assume $Is_15593($Unbox_15532(read(old($Heap), x#0, _module.Cell.fp)), 
          TSet(Tclass._module.Cell()))
         && Set#IsMember($Unbox_15532(read(old($Heap), x#0, _module.Cell.fp)), $Box_11205(y#0))
       ==> $Is_11208(y#0, Tclass._module.Cell());
    assume $Box_15550($Unbox_15532(read($Heap, x#0, _module.Cell.fp)))
       == read($Heap, x#0, _module.Cell.fp);
    assume $Is_15593($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), TSet(Tclass._module.Cell()))
         && Set#IsMember($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), $Box_11205(x#0))
       ==> $Is_11208(x#0, Tclass._module.Cell());
    assume $Is_15593($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), TSet(Tclass._module.Cell()))
         && Set#IsMember($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), $Box_11205(y#0))
       ==> $Is_11208(y#0, Tclass._module.Cell());
    assume $Box_15550($Unbox_15532(read(old($Heap), y#0, _module.Cell.fp)))
       == read(old($Heap), y#0, _module.Cell.fp);
    assume $Is_15593($Unbox_15532(read(old($Heap), y#0, _module.Cell.fp)), 
          TSet(Tclass._module.Cell()))
         && Set#IsMember($Unbox_15532(read(old($Heap), y#0, _module.Cell.fp)), $Box_11205(x#0))
       ==> $Is_11208(x#0, Tclass._module.Cell());
    assume $Is_15593($Unbox_15532(read(old($Heap), y#0, _module.Cell.fp)), 
          TSet(Tclass._module.Cell()))
         && Set#IsMember($Unbox_15532(read(old($Heap), y#0, _module.Cell.fp)), $Box_11205(y#0))
       ==> $Is_11208(y#0, Tclass._module.Cell());
    assume $Box_15550($Unbox_15532(read($Heap, y#0, _module.Cell.fp)))
       == read($Heap, y#0, _module.Cell.fp);
    assume $Is_15593($Unbox_15532(read($Heap, y#0, _module.Cell.fp)), TSet(Tclass._module.Cell()))
         && Set#IsMember($Unbox_15532(read($Heap, y#0, _module.Cell.fp)), $Box_11205(x#0))
       ==> $Is_11208(x#0, Tclass._module.Cell());
    assume $Is_15593($Unbox_15532(read($Heap, y#0, _module.Cell.fp)), TSet(Tclass._module.Cell()))
         && Set#IsMember($Unbox_15532(read($Heap, y#0, _module.Cell.fp)), $Box_11205(y#0))
       ==> $Is_11208(y#0, Tclass._module.Cell());
    assume $Unbox_11205($Box_11205(null)) == null
       && ($IsGoodHeap(old($Heap)) && $Is_11208(x#0, Tclass._module.Cell())
         ==> (_module.__default.Observe#requires(old($Heap), x#0) <==> true))
       && (_module.__default.Observe#requires(old($Heap), x#0)
         ==> _module.__default.Observe#canCall(old($Heap), x#0))
       && ($IsGoodHeap($Heap) && $Is_11208(x#0, Tclass._module.Cell())
         ==> (_module.__default.Observe#requires($Heap, x#0) <==> true))
       && (_module.__default.Observe#requires($Heap, x#0)
         ==> _module.__default.Observe#canCall($Heap, x#0));
    assume $Is_11208(x#0, Tclass._module.Cell())
         && 
        Set#Equal(Set#Intersection(Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
              Set#UnionOne(Set#Empty(), $Box_11205(null))), 
            Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
                $Unbox_15532(read(old($Heap), x#0, _module.Cell.fp))), 
              Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
          Set#Empty())
         && Set#Equal(Set#Intersection(Set#Difference($Alloc, old($Alloc)), 
            Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
                $Unbox_15532(read(old($Heap), x#0, _module.Cell.fp))), 
              Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
          Set#Empty())
       ==> _module.__default.Observe(reveal__module._default.Observe, old($Heap), x#0)
         == _module.__default.Observe(reveal__module._default.Observe, $Heap, x#0);
    assume $Is_11208(x#0, Tclass._module.Cell())
         && 
        Set#Equal(Set#Intersection(Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
              Set#UnionOne(Set#Empty(), $Box_11205(null))), 
            Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
                $Unbox_15532(read(old($Heap), x#0, _module.Cell.fp))), 
              Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
          Set#Empty())
         && Set#Equal(Set#Intersection(Set#Difference($Alloc, old($Alloc)), 
            Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
                $Unbox_15532(read(old($Heap), x#0, _module.Cell.fp))), 
              Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
          Set#Empty())
       ==> Set#Equal(Set#Union(Set#Empty(), 
          Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
              $Unbox_15532(read(old($Heap), x#0, _module.Cell.fp))), 
            Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
        Set#Union(Set#Empty(), 
          Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
              $Unbox_15532(read($Heap, x#0, _module.Cell.fp))), 
            Set#UnionOne(Set#Empty(), $Box_11205(null)))));
    assume ($IsGoodHeap(old($Heap)) && $Is_11208(y#0, Tclass._module.Cell())
         ==> (_module.__default.Observe#requires(old($Heap), y#0) <==> true))
       && (_module.__default.Observe#requires(old($Heap), y#0)
         ==> _module.__default.Observe#canCall(old($Heap), y#0))
       && ($IsGoodHeap($Heap) && $Is_11208(y#0, Tclass._module.Cell())
         ==> (_module.__default.Observe#requires($Heap, y#0) <==> true))
       && (_module.__default.Observe#requires($Heap, y#0)
         ==> _module.__default.Observe#canCall($Heap, y#0));
    assume $Is_11208(y#0, Tclass._module.Cell())
         && 
        Set#Equal(Set#Intersection(Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
              Set#UnionOne(Set#Empty(), $Box_11205(null))), 
            Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
                $Unbox_15532(read(old($Heap), y#0, _module.Cell.fp))), 
              Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
          Set#Empty())
         && Set#Equal(Set#Intersection(Set#Difference($Alloc, old($Alloc)), 
            Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
                $Unbox_15532(read(old($Heap), y#0, _module.Cell.fp))), 
              Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
          Set#Empty())
       ==> _module.__default.Observe(reveal__module._default.Observe, old($Heap), y#0)
         == _module.__default.Observe(reveal__module._default.Observe, $Heap, y#0);
    assume $Is_11208(y#0, Tclass._module.Cell())
         && 
        Set#Equal(Set#Intersection(Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
              Set#UnionOne(Set#Empty(), $Box_11205(null))), 
            Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
                $Unbox_15532(read(old($Heap), y#0, _module.Cell.fp))), 
              Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
          Set#Empty())
         && Set#Equal(Set#Intersection(Set#Difference($Alloc, old($Alloc)), 
            Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
                $Unbox_15532(read(old($Heap), y#0, _module.Cell.fp))), 
              Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
          Set#Empty())
       ==> Set#Equal(Set#Union(Set#Empty(), 
          Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
              $Unbox_15532(read(old($Heap), y#0, _module.Cell.fp))), 
            Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
        Set#Union(Set#Empty(), 
          Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
              $Unbox_15532(read($Heap, y#0, _module.Cell.fp))), 
            Set#UnionOne(Set#Empty(), $Box_11205(null)))));
    assume x#0 != null
         && old($Alloc)[$Box_11205(x#0)]
         && $Is_11208(x#0, Tclass._module.Cell())
       ==> $Is_15593($Unbox_15532(read(old($Heap), x#0, _module.Cell.fp)), 
          TSet(Tclass._module.Cell()))
         && Set#Equal(Set#Difference(Set#Difference($Unbox_15532(read(old($Heap), x#0, _module.Cell.fp)), 
              Set#UnionOne(Set#Empty(), $Box_11205(null))), 
            old($Alloc)), 
          Set#Empty());
    assume x#0 != null
         && old($Alloc)[$Box_11205(x#0)]
         && $Is_11208(x#0, Tclass._module.Cell())
       ==> 0 <= Set#Card($Unbox_15532(read(old($Heap), x#0, _module.Cell.fp)));
    assume x#0 != null
         && old($Alloc)[$Box_11205(x#0)]
         && $Is_11208(x#0, Tclass._module.Cell())
       ==> (Set#Card($Unbox_15532(read(old($Heap), x#0, _module.Cell.fp))) == 0
         <==> Set#Equal($Unbox_15532(read(old($Heap), x#0, _module.Cell.fp)), Set#Empty()));
    assume x#0 != null && $Alloc[$Box_11205(x#0)] && $Is_11208(x#0, Tclass._module.Cell())
       ==> $Is_15593($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), TSet(Tclass._module.Cell()))
         && Set#Equal(Set#Difference(Set#Difference($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), 
              Set#UnionOne(Set#Empty(), $Box_11205(null))), 
            $Alloc), 
          Set#Empty());
    assume x#0 != null && $Alloc[$Box_11205(x#0)] && $Is_11208(x#0, Tclass._module.Cell())
       ==> 0 <= Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp)));
    assume x#0 != null && $Alloc[$Box_11205(x#0)] && $Is_11208(x#0, Tclass._module.Cell())
       ==> (Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp))) == 0
         <==> Set#Equal($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), Set#Empty()));
    assume x#0 != null
         && !Set#IsMember(Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
            Set#UnionOne(Set#Empty(), $Box_11205(null))), 
          $Box_11205(x#0))
         && old($Alloc)[$Box_11205(x#0)]
       ==> read(old($Heap), x#0, _module.Cell.fp) == read($Heap, x#0, _module.Cell.fp);
    assume x#0 != null
         && !Set#IsMember(Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
            Set#UnionOne(Set#Empty(), $Box_11205(null))), 
          $Box_11205(x#0))
         && old($Alloc)[$Box_11205(x#0)]
       ==> read(old($Heap), x#0, _module.Cell.value)
         == read($Heap, x#0, _module.Cell.value);
    assume y#0 != null
         && old($Alloc)[$Box_11205(y#0)]
         && $Is_11208(y#0, Tclass._module.Cell())
       ==> $Is_15593($Unbox_15532(read(old($Heap), y#0, _module.Cell.fp)), 
          TSet(Tclass._module.Cell()))
         && Set#Equal(Set#Difference(Set#Difference($Unbox_15532(read(old($Heap), y#0, _module.Cell.fp)), 
              Set#UnionOne(Set#Empty(), $Box_11205(null))), 
            old($Alloc)), 
          Set#Empty());
    assume y#0 != null
         && old($Alloc)[$Box_11205(y#0)]
         && $Is_11208(y#0, Tclass._module.Cell())
       ==> 0 <= Set#Card($Unbox_15532(read(old($Heap), y#0, _module.Cell.fp)));
    assume y#0 != null
         && old($Alloc)[$Box_11205(y#0)]
         && $Is_11208(y#0, Tclass._module.Cell())
       ==> (Set#Card($Unbox_15532(read(old($Heap), y#0, _module.Cell.fp))) == 0
         <==> Set#Equal($Unbox_15532(read(old($Heap), y#0, _module.Cell.fp)), Set#Empty()));
    assume y#0 != null && $Alloc[$Box_11205(y#0)] && $Is_11208(y#0, Tclass._module.Cell())
       ==> $Is_15593($Unbox_15532(read($Heap, y#0, _module.Cell.fp)), TSet(Tclass._module.Cell()))
         && Set#Equal(Set#Difference(Set#Difference($Unbox_15532(read($Heap, y#0, _module.Cell.fp)), 
              Set#UnionOne(Set#Empty(), $Box_11205(null))), 
            $Alloc), 
          Set#Empty());
    assume y#0 != null && $Alloc[$Box_11205(y#0)] && $Is_11208(y#0, Tclass._module.Cell())
       ==> 0 <= Set#Card($Unbox_15532(read($Heap, y#0, _module.Cell.fp)));
    assume y#0 != null && $Alloc[$Box_11205(y#0)] && $Is_11208(y#0, Tclass._module.Cell())
       ==> (Set#Card($Unbox_15532(read($Heap, y#0, _module.Cell.fp))) == 0
         <==> Set#Equal($Unbox_15532(read($Heap, y#0, _module.Cell.fp)), Set#Empty()));
    assume y#0 != null
         && !Set#IsMember(Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
            Set#UnionOne(Set#Empty(), $Box_11205(null))), 
          $Box_11205(y#0))
         && old($Alloc)[$Box_11205(y#0)]
       ==> read(old($Heap), y#0, _module.Cell.fp) == read($Heap, y#0, _module.Cell.fp);
    assume y#0 != null
         && !Set#IsMember(Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
            Set#UnionOne(Set#Empty(), $Box_11205(null))), 
          $Box_11205(y#0))
         && old($Alloc)[$Box_11205(y#0)]
       ==> read(old($Heap), y#0, _module.Cell.value)
         == read($Heap, y#0, _module.Cell.value);
    assume true;
    return;
}



procedure {:verboseName "Test (call)"} Call$$_module.__default.Test(x#0: ref
       where ($Is_11208(x#0, Tclass._module.Cell())
           <==> $Is_11208(x#0, Tclass._module.Cell?()) && x#0 != null)
         && $Unbox_11205($Box_11205(x#0)) == x#0
         && ($Is_11208(x#0, Tclass._module.Cell?())
           <==> x#0 == null || dtype(x#0) == Tclass._module.Cell?())
         && 
        $Is_11208(x#0, Tclass._module.Cell())
         && (x#0 == null || $Alloc[$Box_11205(x#0)]), 
    y#0: ref
       where ($Is_11208(y#0, Tclass._module.Cell())
           <==> $Is_11208(y#0, Tclass._module.Cell?()) && y#0 != null)
         && $Unbox_11205($Box_11205(y#0)) == y#0
         && ($Is_11208(y#0, Tclass._module.Cell?())
           <==> y#0 == null || dtype(y#0) == Tclass._module.Cell?())
         && 
        $Is_11208(y#0, Tclass._module.Cell())
         && (y#0 == null || $Alloc[$Box_11205(y#0)]));
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id15"} x#0 != y#0;
  free requires {:always_assume} true;
  requires {:id "id16"} !Set#IsMember($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), $Box_11205(y#0));
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires true;
  free requires true;
  free requires true;
  free requires $Box_15550($Unbox_15532(read($Heap, x#0, _module.Cell.fp)))
       == read($Heap, x#0, _module.Cell.fp)
     && $Unbox_11205($Box_11205(y#0)) == y#0;
  free requires true;
  modifies $Heap, $Alloc;



procedure {:verboseName "Test (correctness)"} Impl$$_module.__default.Test(x#0: ref
       where ($Is_11208(x#0, Tclass._module.Cell())
           <==> $Is_11208(x#0, Tclass._module.Cell?()) && x#0 != null)
         && $Unbox_11205($Box_11205(x#0)) == x#0
         && ($Is_11208(x#0, Tclass._module.Cell?())
           <==> x#0 == null || dtype(x#0) == Tclass._module.Cell?())
         && 
        $Is_11208(x#0, Tclass._module.Cell())
         && (x#0 == null || $Alloc[$Box_11205(x#0)]), 
    y#0: ref
       where ($Is_11208(y#0, Tclass._module.Cell())
           <==> $Is_11208(y#0, Tclass._module.Cell?()) && y#0 != null)
         && $Unbox_11205($Box_11205(y#0)) == y#0
         && ($Is_11208(y#0, Tclass._module.Cell?())
           <==> y#0 == null || dtype(y#0) == Tclass._module.Cell?())
         && 
        $Is_11208(y#0, Tclass._module.Cell())
         && (y#0 == null || $Alloc[$Box_11205(y#0)]))
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} true;
  requires {:id "id17"} x#0 != y#0;
  free requires {:always_assume} true;
  requires {:id "id18"} !Set#IsMember($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), $Box_11205(y#0));
  // user-defined frame expressions
  free requires {:always_assume} true;
  free requires true;
  free requires true;
  free requires true;
  free requires $Box_15550($Unbox_15532(read($Heap, x#0, _module.Cell.fp)))
       == read($Heap, x#0, _module.Cell.fp)
     && $Unbox_11205($Box_11205(y#0)) == y#0;
  free requires true;
  modifies $Heap, $Alloc;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "Test (correctness)"} Impl$$_module.__default.Test(x#0: ref, y#0: ref) returns ($_reverifyPost: bool)
{
  var $qfFrameSet#1: [Box]bool;
  var $qfFrameAlloc#1: [Box]bool;
  var before#0: int;
  var ##x#0: ref;
  var y##0: ref;
  var $PreCallHeap#0: [ref][Field]Box;
  var $PreCallAlloc#0: [Box]bool;
  var $qfSubsetField#0: Field;
  var ##x#1: ref;

  anon0:
    // AddMethodImpl: Test, Impl$$_module.__default.Test
    assume $Unbox_11205($Box_11205(y#0)) == y#0 && $Unbox_11205($Box_11205(null)) == null;
    $qfFrameSet#1 := Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
      Set#UnionOne(Set#Empty(), $Box_11205(null)));
    $qfFrameAlloc#1 := $Alloc;
    assume {:captureState "example.dfy(21,0): initial state"} true;
    assume $Box_15550($Unbox_15532(read($Heap, x#0, _module.Cell.fp)))
       == read($Heap, x#0, _module.Cell.fp);
    assume x#0 != y#0 ==> 0 <= Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp)));
    assume x#0 != y#0
       ==> (Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp))) == 0
         <==> Set#Equal($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), Set#Empty()));
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/saline/development/projects/dafny/example.dfy(22,20)
    assume true;
    ##x#0 := x#0;
    // assume allocatedness for argument to function
    assume $Unbox_11205($Box_11205(##x#0)) == ##x#0;
    assume ##x#0 == null || $Alloc[$Box_11205(##x#0)];
    assume ($IsGoodHeap($Heap) && $Is_11208(x#0, Tclass._module.Cell())
         ==> (_module.__default.Observe#requires($Heap, x#0) <==> true))
       && (_module.__default.Observe#requires($Heap, x#0)
         ==> _module.__default.Observe#canCall($Heap, x#0))
       && ($Is_11208(x#0, Tclass._module.Cell())
         <==> $Is_11208(x#0, Tclass._module.Cell?()) && x#0 != null)
       && ($Is_11208(x#0, Tclass._module.Cell?())
         <==> x#0 == null || dtype(x#0) == Tclass._module.Cell?());
    assume _module.__default.Observe#canCall($Heap, x#0);
    assume _module.__default.Observe#canCall($Heap, x#0);
    before#0 := _module.__default.Observe(reveal__module._default.Observe, $Heap, x#0);
    assume {:captureState "example.dfy(22,32)"} true;
    // ----- call statement ----- /Users/saline/development/projects/dafny/example.dfy(23,9)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    y##0 := y#0;
    $PreCallHeap#0 := $Heap;
    $PreCallAlloc#0 := $Alloc;
    assume true;
    assume $Unbox_11205($Box_11205(y##0)) == y##0 && $Unbox_11205($Box_11205(null)) == null;
    assert {:id "id20"} Set#Equal(Set#Difference(Set#Intersection(Set#Union(Set#Empty(), 
            Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y##0)), 
              Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
          $qfFrameAlloc#1), 
        Set#Union(Set#Empty(), $qfFrameSet#1)), 
      Set#Empty());
    call {:id "id21"} Call$$_module.__default.Change(y##0);
    // qf-call-frame Change: full reads supports
    assume Set#Equal(Set#Difference($PreCallAlloc#0, $Alloc), Set#Empty());
    assume $Box_15550($Unbox_15532(read($PreCallHeap#0, x#0, _module.Cell.fp)))
         == read($PreCallHeap#0, x#0, _module.Cell.fp)
       && Inv0_TSet(TSet(Tclass._module.Cell())) == Tclass._module.Cell()
       && Tag(TSet(Tclass._module.Cell())) == TagSet
       && $Unbox_11205($Box_11205(x#0)) == x#0
       && ($Is_11208(x#0, Tclass._module.Cell())
         <==> $Is_11208(x#0, Tclass._module.Cell?()) && x#0 != null)
       && ($Is_11208(x#0, Tclass._module.Cell?())
         <==> x#0 == null || dtype(x#0) == Tclass._module.Cell?());
    assume $Is_15593($Unbox_15532(read($PreCallHeap#0, x#0, _module.Cell.fp)), 
          TSet(Tclass._module.Cell()))
         && Set#IsMember($Unbox_15532(read($PreCallHeap#0, x#0, _module.Cell.fp)), $Box_11205(x#0))
       ==> $Is_11208(x#0, Tclass._module.Cell());
    assume $Unbox_11205($Box_11205(y#0)) == y#0
       && ($Is_11208(y#0, Tclass._module.Cell())
         <==> $Is_11208(y#0, Tclass._module.Cell?()) && y#0 != null)
       && ($Is_11208(y#0, Tclass._module.Cell?())
         <==> y#0 == null || dtype(y#0) == Tclass._module.Cell?());
    assume $Is_15593($Unbox_15532(read($PreCallHeap#0, x#0, _module.Cell.fp)), 
          TSet(Tclass._module.Cell()))
         && Set#IsMember($Unbox_15532(read($PreCallHeap#0, x#0, _module.Cell.fp)), $Box_11205(y#0))
       ==> $Is_11208(y#0, Tclass._module.Cell());
    assume $Box_15550($Unbox_15532(read($Heap, x#0, _module.Cell.fp)))
       == read($Heap, x#0, _module.Cell.fp);
    assume $Is_15593($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), TSet(Tclass._module.Cell()))
         && Set#IsMember($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), $Box_11205(x#0))
       ==> $Is_11208(x#0, Tclass._module.Cell());
    assume $Is_15593($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), TSet(Tclass._module.Cell()))
         && Set#IsMember($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), $Box_11205(y#0))
       ==> $Is_11208(y#0, Tclass._module.Cell());
    assume $Box_15550($Unbox_15532(read($PreCallHeap#0, y#0, _module.Cell.fp)))
       == read($PreCallHeap#0, y#0, _module.Cell.fp);
    assume $Is_15593($Unbox_15532(read($PreCallHeap#0, y#0, _module.Cell.fp)), 
          TSet(Tclass._module.Cell()))
         && Set#IsMember($Unbox_15532(read($PreCallHeap#0, y#0, _module.Cell.fp)), $Box_11205(x#0))
       ==> $Is_11208(x#0, Tclass._module.Cell());
    assume $Is_15593($Unbox_15532(read($PreCallHeap#0, y#0, _module.Cell.fp)), 
          TSet(Tclass._module.Cell()))
         && Set#IsMember($Unbox_15532(read($PreCallHeap#0, y#0, _module.Cell.fp)), $Box_11205(y#0))
       ==> $Is_11208(y#0, Tclass._module.Cell());
    assume $Box_15550($Unbox_15532(read($Heap, y#0, _module.Cell.fp)))
       == read($Heap, y#0, _module.Cell.fp);
    assume $Is_15593($Unbox_15532(read($Heap, y#0, _module.Cell.fp)), TSet(Tclass._module.Cell()))
         && Set#IsMember($Unbox_15532(read($Heap, y#0, _module.Cell.fp)), $Box_11205(x#0))
       ==> $Is_11208(x#0, Tclass._module.Cell());
    assume $Is_15593($Unbox_15532(read($Heap, y#0, _module.Cell.fp)), TSet(Tclass._module.Cell()))
         && Set#IsMember($Unbox_15532(read($Heap, y#0, _module.Cell.fp)), $Box_11205(y#0))
       ==> $Is_11208(y#0, Tclass._module.Cell());
    assume $Unbox_11205($Box_11205(null)) == null
       && ($IsGoodHeap($PreCallHeap#0) && $Is_11208(x#0, Tclass._module.Cell())
         ==> (_module.__default.Observe#requires($PreCallHeap#0, x#0) <==> true))
       && (_module.__default.Observe#requires($PreCallHeap#0, x#0)
         ==> _module.__default.Observe#canCall($PreCallHeap#0, x#0))
       && ($IsGoodHeap($Heap) && $Is_11208(x#0, Tclass._module.Cell())
         ==> (_module.__default.Observe#requires($Heap, x#0) <==> true))
       && (_module.__default.Observe#requires($Heap, x#0)
         ==> _module.__default.Observe#canCall($Heap, x#0));
    assume $Is_11208(x#0, Tclass._module.Cell())
         && 
        Set#Equal(Set#Intersection(Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
              Set#UnionOne(Set#Empty(), $Box_11205(null))), 
            Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
                $Unbox_15532(read($PreCallHeap#0, x#0, _module.Cell.fp))), 
              Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
          Set#Empty())
         && Set#Equal(Set#Intersection(Set#Difference($Alloc, $PreCallAlloc#0), 
            Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
                $Unbox_15532(read($PreCallHeap#0, x#0, _module.Cell.fp))), 
              Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
          Set#Empty())
       ==> _module.__default.Observe(reveal__module._default.Observe, $PreCallHeap#0, x#0)
         == _module.__default.Observe(reveal__module._default.Observe, $Heap, x#0);
    assume $Is_11208(x#0, Tclass._module.Cell())
         && 
        Set#Equal(Set#Intersection(Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
              Set#UnionOne(Set#Empty(), $Box_11205(null))), 
            Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
                $Unbox_15532(read($PreCallHeap#0, x#0, _module.Cell.fp))), 
              Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
          Set#Empty())
         && Set#Equal(Set#Intersection(Set#Difference($Alloc, $PreCallAlloc#0), 
            Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
                $Unbox_15532(read($PreCallHeap#0, x#0, _module.Cell.fp))), 
              Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
          Set#Empty())
       ==> Set#Equal(Set#Union(Set#Empty(), 
          Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
              $Unbox_15532(read($PreCallHeap#0, x#0, _module.Cell.fp))), 
            Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
        Set#Union(Set#Empty(), 
          Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(x#0)), 
              $Unbox_15532(read($Heap, x#0, _module.Cell.fp))), 
            Set#UnionOne(Set#Empty(), $Box_11205(null)))));
    assume ($IsGoodHeap($PreCallHeap#0) && $Is_11208(y#0, Tclass._module.Cell())
         ==> (_module.__default.Observe#requires($PreCallHeap#0, y#0) <==> true))
       && (_module.__default.Observe#requires($PreCallHeap#0, y#0)
         ==> _module.__default.Observe#canCall($PreCallHeap#0, y#0))
       && ($IsGoodHeap($Heap) && $Is_11208(y#0, Tclass._module.Cell())
         ==> (_module.__default.Observe#requires($Heap, y#0) <==> true))
       && (_module.__default.Observe#requires($Heap, y#0)
         ==> _module.__default.Observe#canCall($Heap, y#0));
    assume $Is_11208(y#0, Tclass._module.Cell())
         && 
        Set#Equal(Set#Intersection(Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
              Set#UnionOne(Set#Empty(), $Box_11205(null))), 
            Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
                $Unbox_15532(read($PreCallHeap#0, y#0, _module.Cell.fp))), 
              Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
          Set#Empty())
         && Set#Equal(Set#Intersection(Set#Difference($Alloc, $PreCallAlloc#0), 
            Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
                $Unbox_15532(read($PreCallHeap#0, y#0, _module.Cell.fp))), 
              Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
          Set#Empty())
       ==> _module.__default.Observe(reveal__module._default.Observe, $PreCallHeap#0, y#0)
         == _module.__default.Observe(reveal__module._default.Observe, $Heap, y#0);
    assume $Is_11208(y#0, Tclass._module.Cell())
         && 
        Set#Equal(Set#Intersection(Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
              Set#UnionOne(Set#Empty(), $Box_11205(null))), 
            Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
                $Unbox_15532(read($PreCallHeap#0, y#0, _module.Cell.fp))), 
              Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
          Set#Empty())
         && Set#Equal(Set#Intersection(Set#Difference($Alloc, $PreCallAlloc#0), 
            Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
                $Unbox_15532(read($PreCallHeap#0, y#0, _module.Cell.fp))), 
              Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
          Set#Empty())
       ==> Set#Equal(Set#Union(Set#Empty(), 
          Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
              $Unbox_15532(read($PreCallHeap#0, y#0, _module.Cell.fp))), 
            Set#UnionOne(Set#Empty(), $Box_11205(null)))), 
        Set#Union(Set#Empty(), 
          Set#Difference(Set#Union(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
              $Unbox_15532(read($Heap, y#0, _module.Cell.fp))), 
            Set#UnionOne(Set#Empty(), $Box_11205(null)))));
    assume x#0 != null
         && $PreCallAlloc#0[$Box_11205(x#0)]
         && $Is_11208(x#0, Tclass._module.Cell())
       ==> $Is_15593($Unbox_15532(read($PreCallHeap#0, x#0, _module.Cell.fp)), 
          TSet(Tclass._module.Cell()))
         && Set#Equal(Set#Difference(Set#Difference($Unbox_15532(read($PreCallHeap#0, x#0, _module.Cell.fp)), 
              Set#UnionOne(Set#Empty(), $Box_11205(null))), 
            $PreCallAlloc#0), 
          Set#Empty());
    assume x#0 != null
         && $PreCallAlloc#0[$Box_11205(x#0)]
         && $Is_11208(x#0, Tclass._module.Cell())
       ==> 0 <= Set#Card($Unbox_15532(read($PreCallHeap#0, x#0, _module.Cell.fp)));
    assume x#0 != null
         && $PreCallAlloc#0[$Box_11205(x#0)]
         && $Is_11208(x#0, Tclass._module.Cell())
       ==> (Set#Card($Unbox_15532(read($PreCallHeap#0, x#0, _module.Cell.fp))) == 0
         <==> Set#Equal($Unbox_15532(read($PreCallHeap#0, x#0, _module.Cell.fp)), Set#Empty()));
    assume x#0 != null && $Alloc[$Box_11205(x#0)] && $Is_11208(x#0, Tclass._module.Cell())
       ==> $Is_15593($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), TSet(Tclass._module.Cell()))
         && Set#Equal(Set#Difference(Set#Difference($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), 
              Set#UnionOne(Set#Empty(), $Box_11205(null))), 
            $Alloc), 
          Set#Empty());
    assume x#0 != null && $Alloc[$Box_11205(x#0)] && $Is_11208(x#0, Tclass._module.Cell())
       ==> 0 <= Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp)));
    assume x#0 != null && $Alloc[$Box_11205(x#0)] && $Is_11208(x#0, Tclass._module.Cell())
       ==> (Set#Card($Unbox_15532(read($Heap, x#0, _module.Cell.fp))) == 0
         <==> Set#Equal($Unbox_15532(read($Heap, x#0, _module.Cell.fp)), Set#Empty()));
    assume x#0 != null
         && !Set#IsMember(Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
            Set#UnionOne(Set#Empty(), $Box_11205(null))), 
          $Box_11205(x#0))
         && $PreCallAlloc#0[$Box_11205(x#0)]
       ==> read($PreCallHeap#0, x#0, _module.Cell.fp) == read($Heap, x#0, _module.Cell.fp);
    assume x#0 != null
         && !Set#IsMember(Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
            Set#UnionOne(Set#Empty(), $Box_11205(null))), 
          $Box_11205(x#0))
         && $PreCallAlloc#0[$Box_11205(x#0)]
       ==> read($PreCallHeap#0, x#0, _module.Cell.value)
         == read($Heap, x#0, _module.Cell.value);
    assume y#0 != null
         && $PreCallAlloc#0[$Box_11205(y#0)]
         && $Is_11208(y#0, Tclass._module.Cell())
       ==> $Is_15593($Unbox_15532(read($PreCallHeap#0, y#0, _module.Cell.fp)), 
          TSet(Tclass._module.Cell()))
         && Set#Equal(Set#Difference(Set#Difference($Unbox_15532(read($PreCallHeap#0, y#0, _module.Cell.fp)), 
              Set#UnionOne(Set#Empty(), $Box_11205(null))), 
            $PreCallAlloc#0), 
          Set#Empty());
    assume y#0 != null
         && $PreCallAlloc#0[$Box_11205(y#0)]
         && $Is_11208(y#0, Tclass._module.Cell())
       ==> 0 <= Set#Card($Unbox_15532(read($PreCallHeap#0, y#0, _module.Cell.fp)));
    assume y#0 != null
         && $PreCallAlloc#0[$Box_11205(y#0)]
         && $Is_11208(y#0, Tclass._module.Cell())
       ==> (Set#Card($Unbox_15532(read($PreCallHeap#0, y#0, _module.Cell.fp))) == 0
         <==> Set#Equal($Unbox_15532(read($PreCallHeap#0, y#0, _module.Cell.fp)), Set#Empty()));
    assume y#0 != null && $Alloc[$Box_11205(y#0)] && $Is_11208(y#0, Tclass._module.Cell())
       ==> $Is_15593($Unbox_15532(read($Heap, y#0, _module.Cell.fp)), TSet(Tclass._module.Cell()))
         && Set#Equal(Set#Difference(Set#Difference($Unbox_15532(read($Heap, y#0, _module.Cell.fp)), 
              Set#UnionOne(Set#Empty(), $Box_11205(null))), 
            $Alloc), 
          Set#Empty());
    assume y#0 != null && $Alloc[$Box_11205(y#0)] && $Is_11208(y#0, Tclass._module.Cell())
       ==> 0 <= Set#Card($Unbox_15532(read($Heap, y#0, _module.Cell.fp)));
    assume y#0 != null && $Alloc[$Box_11205(y#0)] && $Is_11208(y#0, Tclass._module.Cell())
       ==> (Set#Card($Unbox_15532(read($Heap, y#0, _module.Cell.fp))) == 0
         <==> Set#Equal($Unbox_15532(read($Heap, y#0, _module.Cell.fp)), Set#Empty()));
    assume y#0 != null
         && !Set#IsMember(Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
            Set#UnionOne(Set#Empty(), $Box_11205(null))), 
          $Box_11205(y#0))
         && $PreCallAlloc#0[$Box_11205(y#0)]
       ==> read($PreCallHeap#0, y#0, _module.Cell.fp) == read($Heap, y#0, _module.Cell.fp);
    assume y#0 != null
         && !Set#IsMember(Set#Difference(Set#UnionOne(Set#Empty(), $Box_11205(y#0)), 
            Set#UnionOne(Set#Empty(), $Box_11205(null))), 
          $Box_11205(y#0))
         && $PreCallAlloc#0[$Box_11205(y#0)]
       ==> read($PreCallHeap#0, y#0, _module.Cell.value)
         == read($Heap, y#0, _module.Cell.value);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "example.dfy(23,11)"} true;
    // ----- assert statement ----- /Users/saline/development/projects/dafny/example.dfy(24,3)
    ##x#1 := x#0;
    // assume allocatedness for argument to function
    assume $Unbox_11205($Box_11205(##x#1)) == ##x#1;
    assume ##x#1 == null || $Alloc[$Box_11205(##x#1)];
    assume ($IsGoodHeap($Heap) && $Is_11208(x#0, Tclass._module.Cell())
         ==> (_module.__default.Observe#requires($Heap, x#0) <==> true))
       && (_module.__default.Observe#requires($Heap, x#0)
         ==> _module.__default.Observe#canCall($Heap, x#0))
       && ($Is_11208(x#0, Tclass._module.Cell())
         <==> $Is_11208(x#0, Tclass._module.Cell?()) && x#0 != null)
       && ($Is_11208(x#0, Tclass._module.Cell?())
         <==> x#0 == null || dtype(x#0) == Tclass._module.Cell?());
    assume _module.__default.Observe#canCall($Heap, x#0);
    assume _module.__default.Observe#canCall($Heap, x#0);
    assert {:id "id22"} _module.__default.Observe(reveal__module._default.Observe, $Heap, x#0)
       == before#0;
    assume true;
    return;
}



procedure {:verboseName "reveal_Observe (well-formedness)"} {:verify false} CheckWellFormed$$_module.__default.reveal__Observe();
  modifies $Heap, $Alloc;



procedure {:verboseName "reveal_Observe (call)"} {:verify false} Call$$_module.__default.reveal__Observe();
  modifies $Heap, $Alloc;
  // frame condition
  free ensures old($Heap) == $Heap;
  free ensures reveal__module._default.Observe;
  free ensures true;
  free ensures true;



const unique class._module.Cell?: ClassName;

function Tclass._module.Cell?() : Ty
uses {
// Tclass._module.Cell? Tag
axiom TagFamily(Tclass._module.Cell?()) == tytagFamily$Cell;
// Tclass._module.Cell? Tag
axiom Tag(Tclass._module.Cell?()) == Tagclass._module.Cell?;
}

const unique Tagclass._module.Cell?: TyTag;

const _module.Cell.value: Field
uses {
axiom !$IsGhostField(_module.Cell.value);
axiom FieldOfDecl(class._module.Cell?, field$value) == _module.Cell.value;
axiom FDim(_module.Cell.value) == 0;
}

const _module.Cell.fp: Field
uses {
axiom $IsGhostField(_module.Cell.fp);
axiom FieldOfDecl(class._module.Cell?, field$fp) == _module.Cell.fp;
axiom FDim(_module.Cell.fp) == 0;
}

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

const unique field$fp: NameFamily;

function {:identity} Lit_13815(x: Box) : Box;

function $Box_331(int) : Box;

function $Box_373(real) : Box;

function $Unbox_637(Box) : int;

function $Unbox_661(Box) : real;

function $Unbox_685(Box) : bool;

function $Box_685(bool) : Box;

function $Unbox_10794(Box) : char;

function $Box_10794(char) : Box;

function $Unbox_15532(Box) : [Box]bool;

function $Box_15550([Box]bool) : Box;

function $Is_15593([Box]bool, Ty) : bool;

function $IsAlloc_15822([Box]bool, Ty, [ref][Field]Box) : bool;

function $Box_10895(DatatypeType) : Box;

function $Is_2(int, Ty) : bool;

function $Unbox_11205(Box) : ref;

function $Box_11205(ref) : Box;

function $Is_11208(ref, Ty) : bool;

function $Unbox_11341(Box) : HandleType;

function $Box_11341(HandleType) : Box;

function $Is_11390(HandleType, Ty) : bool;

function $Unbox_11681(Box) : DatatypeType;

function $Is_11119(DatatypeType, Ty) : bool;

function {:identity} Lit_11119(x: DatatypeType) : DatatypeType;

function {:identity} Lit_331(x: int) : int;

function {:identity} Lit_373(x: real) : real;

function {:identity} Lit_685(x: bool) : bool;

function {:identity} Lit_10794(x: char) : char;

function {:identity} Lit_47848(x: [Box]bool) : [Box]bool;

function {:identity} Lit_11205(x: ref) : ref;

function {:identity} Lit_11341(x: HandleType) : HandleType;

function $Box_13815(Box) : Box;

function $Unbox_13815(Box) : Box;

function $Is_373(real, Ty) : bool;

function $Is_685(bool, Ty) : bool;

function $Is_10794(char, Ty) : bool;

function $Is_13815(Box, Ty) : bool;

axiom true;

axiom true;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} ($Is_11119(#_System._tuple#0._#Make0(), Tclass._System.Tuple0())
     ==> _System.Tuple0.___hMake0_q(#_System._tuple#0._#Make0()))
   && (_System.Tuple0.___hMake0_q(#_System._tuple#0._#Make0())
     <==> DatatypeCtorId(#_System._tuple#0._#Make0()) == ##_System._tuple#0._#Make0)
   && (_System.Tuple0.___hMake0_q(#_System._tuple#0._#Make0())
     ==> #_System._tuple#0._#Make0() == #_System._tuple#0._#Make0());

axiom {:include_dep} Lit_11119(#_System._tuple#0._#Make0()) == #_System._tuple#0._#Make0();

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} DeclType(FieldOfDecl(class._module.Cell?, field$value)) == class._module.Cell?
   && DeclName(FieldOfDecl(class._module.Cell?, field$value)) == field$value;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} DeclType(FieldOfDecl(class._module.Cell?, field$fp)) == class._module.Cell?
   && DeclName(FieldOfDecl(class._module.Cell?, field$fp)) == field$fp;

axiom {:include_dep} true;

axiom {:include_dep} true;

axiom {:include_dep} true;
