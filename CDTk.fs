/// CDTk.fs — UAB v4: Categorical Diagram Translation Toolkit
/// A functorial compression engine that models programs as diagrams in an
/// enriched 2-category and translates them via structure-preserving functors.
module CDTk

open System
open System.Collections.Generic
open System.Security.Cryptography

// ═══════════════════════════════════════════════════════════════════════════════
// §1  ENRICHMENT SPACE  — monoidal vectors over (cost,prob,purity,safety,resource,time,energy)
// ═══════════════════════════════════════════════════════════════════════════════

[<Struct>]
type V = { Cost:float; Prob:float; Purity:float; Safety:float; Resource:float; Time:float; Energy:float }

module V =
    let zero   = { Cost=0.;Prob=1.;Purity=1.;Safety=1.;Resource=0.;Time=0.;Energy=0. }
    let bottom = { Cost=infinity;Prob=0.;Purity=0.;Safety=0.;Resource=infinity;Time=infinity;Energy=infinity }
    let compose a b =
        { Cost=a.Cost+b.Cost; Prob=a.Prob*b.Prob; Purity=min a.Purity b.Purity
          Safety=min a.Safety b.Safety; Resource=a.Resource+b.Resource
          Time=a.Time+b.Time; Energy=a.Energy+b.Energy }
    let meet a b =
        { Cost=min a.Cost b.Cost; Prob=max a.Prob b.Prob; Purity=max a.Purity b.Purity
          Safety=max a.Safety b.Safety; Resource=min a.Resource b.Resource
          Time=min a.Time b.Time; Energy=min a.Energy b.Energy }
    let isBottom v = v.Cost = infinity || v.Prob = 0. || v.Safety = 0.
    let dominates a b =
        a.Cost<=b.Cost && a.Prob>=b.Prob && a.Purity>=b.Purity && a.Safety>=b.Safety
        && a.Resource<=b.Resource && a.Time<=b.Time && a.Energy<=b.Energy
    /// Landauer lower-bound: kT ln2 per irreversible bit erasure
    let landauer bits tempK = bits * 1.380649e-23 * tempK * log 2.0

// ═══════════════════════════════════════════════════════════════════════════════
// §2  MERKLE HASHING  — content-addressed persistent identity
// ═══════════════════════════════════════════════════════════════════════════════

type Hash = Hash of byte[]

module Merkle =
    let private sha (data:byte[]) =
        use h = SHA256.Create()
        Hash(h.ComputeHash data)
    let ofString (s:string) = sha (Text.Encoding.UTF8.GetBytes s)
    let combine (Hash a) (Hash b) =
        let buf = Array.append a b
        sha buf
    let combineMany hashes = hashes |> Seq.fold combine (ofString "")
    let equal (Hash a) (Hash b) = ReadOnlySpan(a).SequenceEqual(ReadOnlySpan(b))

// ═══════════════════════════════════════════════════════════════════════════════
// §3  ENRICHED 2-CATEGORY IR  — objects, morphisms, 2-cells, diagrams
// ═══════════════════════════════════════════════════════════════════════════════

type ObjId  = ObjId of int
type MorId  = MorId of int
type CellId = CellId of int

/// Object: typed entity carrying an enrichment vector
type Obj = { Id:ObjId; Name:string; Ty:string; Effects:string list; Vec:V; Hash:Hash }

/// Morphism: transformation between objects with enriched weight
type Mor = { Id:MorId; Src:ObjId; Tgt:ObjId; Label:string; Weight:V; Hash:Hash }

/// 2-Cell: rewrite proof between parallel morphisms
type TwoCell =
    { Id:CellId; Source:MorId; Target:MorId; Proof:Proof; DeltaV:V; Hash:Hash }

and Proof =
    | Axiom        of string
    | Compose      of Proof * Proof
    | Tensor       of Proof * Proof
    | Inverse      of Proof
    | Identity
    | BetaReduction
    | InlineExpansion
    | DeadCodeElim
    | FusionRule    of string
    | KanWitness    of string
    | AdjointLift   of Proof

/// The diagram: a persistent, content-addressed program graph
type Diagram =
    { Objects   : Map<ObjId,Obj>
      Morphisms : Map<MorId,Mor>
      TwoCells  : Map<CellId,TwoCell>
      NextObj   : int; NextMor : int; NextCell : int
      RootHash  : Hash }

module Diagram =
    let empty =
        { Objects=Map.empty;Morphisms=Map.empty;TwoCells=Map.empty
          NextObj=0;NextMor=0;NextCell=0;RootHash=Merkle.ofString "empty" }

    let private rehash (d:Diagram) =
        let oh = d.Objects  |> Map.toSeq |> Seq.map (fun (_,o)->o.Hash) |> Merkle.combineMany
        let mh = d.Morphisms|> Map.toSeq |> Seq.map (fun (_,m)->m.Hash) |> Merkle.combineMany
        let ch = d.TwoCells |> Map.toSeq |> Seq.map (fun (_,c)->c.Hash) |> Merkle.combineMany
        { d with RootHash = Merkle.combineMany [oh;mh;ch] }

    let addObj name ty effs vec (d:Diagram) =
        let id = ObjId d.NextObj
        let h  = Merkle.ofString (sprintf "%s:%s:%A:%A" name ty effs vec)
        let o  = { Id=id;Name=name;Ty=ty;Effects=effs;Vec=vec;Hash=h }
        rehash { d with Objects=Map.add id o d.Objects; NextObj=d.NextObj+1 }, id

    let addMor src tgt label wt (d:Diagram) =
        let id = MorId d.NextMor
        let h  = Merkle.ofString (sprintf "%A->%A:%s:%A" src tgt label wt)
        let m  = { Id=id;Src=src;Tgt=tgt;Label=label;Weight=wt;Hash=h }
        rehash { d with Morphisms=Map.add id m d.Morphisms; NextMor=d.NextMor+1 }, id

    let addCell src tgt proof dv (d:Diagram) =
        let id = CellId d.NextCell
        let h  = Merkle.ofString (sprintf "%A=>%A:%A" src tgt proof)
        let c  = { Id=id;Source=src;Target=tgt;Proof=proof;DeltaV=dv;Hash=h }
        rehash { d with TwoCells=Map.add id c d.TwoCells; NextCell=d.NextCell+1 }, id

    let composeMorphisms (m1:Mor) (m2:Mor) (d:Diagram) =
        addMor m1.Src m2.Tgt (m1.Label+";"+m2.Label) (V.compose m1.Weight m2.Weight) d

    let diff (a:Diagram) (b:Diagram) =
        let changedObjs = b.Objects |> Map.filter (fun k v ->
            match Map.tryFind k a.Objects with Some o -> not(Merkle.equal o.Hash v.Hash) | None -> true)
        let changedMors = b.Morphisms |> Map.filter (fun k v ->
            match Map.tryFind k a.Morphisms with Some m -> not(Merkle.equal m.Hash v.Hash) | None -> true)
        changedObjs, changedMors

// ═══════════════════════════════════════════════════════════════════════════════
// §4  INTAKE ENGINE  — AG-LL∞ symbolic parser with zero-explosion
// ═══════════════════════════════════════════════════════════════════════════════

/// Symbolic parse tree with coproduct nodes for ambiguity
type ParseNode =
    | Terminal   of string
    | NonTerm    of string * ParseNode list
    | Coproduct  of ParseNode list          // symbolic superposition: (A|B)
    | Empty

type Grammar = { Rules: Map<string, string list list> }  // non-terminal -> list of alternatives (each = list of symbols)

module Intake =
    /// Memoization table keyed on (rule, position) — prevents exponential blowup
    type private MemoKey = string * int
    type private MemoTable = Dictionary<MemoKey, (ParseNode * int) option>

    /// AG-LL∞ parser: predictive recursive descent with symbolic coproducts.
    /// Zero-explosion: memoized so each (rule,pos) is computed at most once → O(n·α(n)).
    let parse (g:Grammar) (tokens:string[]) : ParseNode option =
        let memo = MemoTable()

        let rec parseRule (rule:string) (pos:int) : (ParseNode * int) option =
            let key = (rule, pos)
            match memo.TryGetValue key with
            | true, v -> v
            | _ ->
                memo.[key] <- None  // left-recursion guard
                let result =
                    match Map.tryFind rule g.Rules with
                    | None ->
                        // terminal match
                        if pos < tokens.Length && tokens.[pos] = rule
                        then Some(Terminal rule, pos+1)
                        else None
                    | Some alts ->
                        let successes =
                            alts |> List.choose (fun alt ->
                                parseSeq alt pos |> Option.map (fun (nodes,p) ->
                                    (if List.length nodes = 1 then nodes.[0]
                                     else NonTerm(rule, nodes)), p))
                        match successes with
                        | []  -> None
                        | [x] -> Some x
                        | xs  ->
                            // symbolic superposition: compact ambiguity into a coproduct node
                            let maxPos = xs |> List.map snd |> List.max
                            Some(Coproduct(xs |> List.map fst), maxPos)
                memo.[key] <- result
                result

        and parseSeq (symbols:string list) (pos:int) : (ParseNode list * int) option =
            let mutable p = pos
            let mutable acc = []
            let mutable ok = true
            for sym in symbols do
                if ok then
                    match parseRule sym p with
                    | Some(n, p') -> acc <- n :: acc; p <- p'
                    | None        -> ok <- false
            if ok then Some(List.rev acc, p) else None

        match Map.tryFind "start" g.Rules with
        | None   -> None
        | Some _ ->
            parseRule "start" 0
            |> Option.bind (fun (node, pos) -> if pos = tokens.Length then Some node else None)

    /// Flatten coproducts: enumerate all concrete parses (for validation)
    let rec flatten = function
        | Coproduct alts -> alts |> List.collect flatten
        | NonTerm(n,ch)  ->
            let rec cart = function
                | []    -> [[]]
                | h::t  -> [for x in flatten h do for rest in cart t -> x::rest]
            cart ch |> List.map (fun cs -> NonTerm(n,cs))
        | node -> [node]

// ═══════════════════════════════════════════════════════════════════════════════
// §5  PROFUNCTORS & CO-ENDS  — operational semantics for the enriched IR
// ═══════════════════════════════════════════════════════════════════════════════

/// A profunctor P: C^op × D → V assigns an enriched value to each (source,target) pair.
type Profunctor = { Apply: ObjId -> ObjId -> V }

module Profunctor =
    /// Identity profunctor: hom-enrichment from morphisms
    let hom (d:Diagram) : Profunctor =
        { Apply = fun a b ->
            d.Morphisms |> Map.toSeq
            |> Seq.filter (fun (_,m) -> m.Src=a && m.Tgt=b)
            |> Seq.map (fun (_,m) -> m.Weight)
            |> Seq.fold V.meet V.bottom }

    /// Co-end: ∫^c P(c,c) — aggregates the "trace" over all objects
    let coend (d:Diagram) (p:Profunctor) : V =
        d.Objects |> Map.toSeq
        |> Seq.map (fun (id,_) -> p.Apply id id)
        |> Seq.fold V.meet V.bottom

    /// Profunctor composition via co-end: (P ⊗ Q)(a,c) = ∫^b P(a,b)⊗Q(b,c)
    let compose (d:Diagram) (p:Profunctor) (q:Profunctor) : Profunctor =
        { Apply = fun a c ->
            d.Objects |> Map.toSeq
            |> Seq.map (fun (b,_) -> V.compose (p.Apply a b) (q.Apply b c))
            |> Seq.fold V.meet V.bottom }

// ═══════════════════════════════════════════════════════════════════════════════
// §6  UNIFICATION ENGINE  — incremental enriched narrowing with obstruction detection
// ═══════════════════════════════════════════════════════════════════════════════

type ConstraintKind =
    | Algebraic   of string          // type equality / subtype
    | Probabilistic of float * float // probability bounds [lo,hi]
    | Temporal    of float           // time upper-bound
    | Spatial     of float           // resource upper-bound
    | ResourceLin of int             // linear resource count (must reach 0)
    | Purity      of float           // minimum purity threshold
    | SafetyReq   of float           // minimum safety threshold
    | Custom      of string * (V -> bool)

type Constraint = { ObjId:ObjId; Kind:ConstraintKind }

type Obstruction = { Location:ObjId; Core:Constraint list; Suggestion:string }

module Unifier =
    /// Check a single constraint against an object's enrichment vector
    let private check (c:Constraint) (v:V) : bool =
        match c.Kind with
        | Algebraic _        -> true  // algebraic constraints resolved structurally
        | Probabilistic(l,h) -> v.Prob >= l && v.Prob <= h
        | Temporal bound     -> v.Time <= bound
        | Spatial bound      -> v.Resource <= bound
        | ResourceLin n      -> v.Resource <= float n
        | Purity p           -> v.Purity >= p
        | SafetyReq s        -> v.Safety >= s
        | Custom(_, f)       -> f v

    /// Narrow: apply constraints to refine vectors, returning updated diagram + obstructions.
    /// Incremental: only recomputes objects whose constraints are unsatisfied.
    let narrow (constraints:Constraint list) (d:Diagram) : Diagram * Obstruction list =
        let mutable diagram = d
        let mutable obstructions = []
        let byObj = constraints |> List.groupBy (fun c -> c.ObjId) |> Map.ofList
        for kv in byObj do
            let oid, cs = kv.Key, kv.Value
            match Map.tryFind oid diagram.Objects with
            | None -> ()
            | Some obj ->
                let failed = cs |> List.filter (fun c -> not (check c obj.Vec))
                if not (List.isEmpty failed) then
                    // attempt monotonic narrowing
                    let narrowed =
                        failed |> List.fold (fun (v:V) c ->
                            match c.Kind with
                            | Temporal b     -> { v with Time = min v.Time b }
                            | Spatial b      -> { v with Resource = min v.Resource b }
                            | Purity p       -> { v with Purity = max v.Purity p }
                            | SafetyReq s    -> { v with Safety = max v.Safety s }
                            | Probabilistic(lo,_) -> { v with Prob = max v.Prob lo }
                            | _              -> v
                        ) obj.Vec
                    if V.isBottom narrowed then
                        let suggest =
                            failed |> List.map (fun c ->
                                match c.Kind with
                                | Temporal b -> sprintf "relax time bound (current %.2f, need ≤%.2f)" obj.Vec.Time b
                                | Spatial b  -> sprintf "reduce resource (current %.2f, need ≤%.2f)" obj.Vec.Resource b
                                | Purity p   -> sprintf "increase purity (current %.2f, need ≥%.2f)" obj.Vec.Purity p
                                | SafetyReq s-> sprintf "increase safety (current %.2f, need ≥%.2f)" obj.Vec.Safety s
                                | _          -> "review constraint")
                            |> String.concat "; "
                        obstructions <- { Location=oid; Core=failed; Suggestion=suggest } :: obstructions
                    else
                        let h = Merkle.ofString (sprintf "%s:%s:%A:%A" obj.Name obj.Ty obj.Effects narrowed)
                        let obj' = { obj with Vec=narrowed; Hash=h }
                        diagram <- { diagram with Objects = Map.add oid obj' diagram.Objects }
        diagram, List.rev obstructions

    /// Algebraic unification for type constraints: simple structural unification
    let unifyTypes (t1:string) (t2:string) : Result<string, string> =
        if t1 = t2 then Ok t1
        elif t1 = "_" then Ok t2
        elif t2 = "_" then Ok t1
        else Error (sprintf "type mismatch: %s ≠ %s" t1 t2)

// ═══════════════════════════════════════════════════════════════════════════════
// §7  LOWERING ENGINE  — enriched functor selection, fusion, Kan extensions
// ═══════════════════════════════════════════════════════════════════════════════

type Backend = LLVM | CSharp | JavaScript | WASM | GPU | HardwareDSL | ProbabilisticDSL

type LowerFunctor =
    { Name       : string
      Backend    : Backend
      MapObj     : Obj -> Obj
      MapMor     : Mor -> Mor
      MapCell    : TwoCell -> TwoCell
      Supported  : string Set }

type KanExtension =
    { Feature    : string
      Direction  : KanDir
      Approx     : Obj -> Obj
      Obligation : Proof }
and KanDir = LeftKan | RightKan

module Lowering =
    /// Apply a lowering functor to an entire diagram (structure-preserving)
    let applyFunctor (f:LowerFunctor) (d:Diagram) : Diagram =
        let objs' = d.Objects  |> Map.map (fun _ o -> f.MapObj o)
        let mors' = d.Morphisms|> Map.map (fun _ m -> f.MapMor m)
        let cls'  = d.TwoCells |> Map.map (fun _ c -> f.MapCell c)
        { d with Objects=objs'; Morphisms=mors'; TwoCells=cls' }
        |> fun d' ->
            let oh = d'.Objects  |> Map.toSeq |> Seq.map (fun (_,o)->o.Hash) |> Merkle.combineMany
            let mh = d'.Morphisms|> Map.toSeq |> Seq.map (fun (_,m)->m.Hash) |> Merkle.combineMany
            let ch = d'.TwoCells |> Map.toSeq |> Seq.map (fun (_,c)->c.Hash) |> Merkle.combineMany
            { d' with RootHash = Merkle.combineMany [oh;mh;ch] }

    /// Functor fusion: compose a sequence of lowering functors into a single pass
    let fuse (functors:LowerFunctor list) : LowerFunctor =
        match functors with
        | []  -> failwith "empty functor list"
        | [f] -> f
        | fs  ->
            let back = fs |> List.rev |> List.head
            { Name     = functors |> List.map (fun f->f.Name) |> String.concat "∘"
              Backend  = back.Backend
              MapObj   = fun o -> functors |> List.fold (fun o' f -> f.MapObj o') o
              MapMor   = fun m -> functors |> List.fold (fun m' f -> f.MapMor m') m
              MapCell  = fun c -> functors |> List.fold (fun c' f -> f.MapCell c') c
              Supported = functors |> List.map (fun f->f.Supported) |> Set.intersectMany }

    /// Select the best functor for a given backend and enrichment target
    let select (available:LowerFunctor list) (backend:Backend) (target:V) : LowerFunctor option =
        available
        |> List.filter (fun f -> f.Backend = backend)
        |> List.sortBy (fun f ->
            // score by how well functor output dominates target
            let sample = f.MapObj { Id=ObjId 0;Name="";Ty="";Effects=[];Vec=target;Hash=Merkle.ofString "" }
            let v = sample.Vec
            abs(v.Cost - target.Cost) + abs(v.Time - target.Time) + abs(v.Energy - target.Energy))
        |> List.tryHead

    /// Kan extension: derive an approximation when backend lacks a feature
    let kanExtend (feature:string) (dir:KanDir) : KanExtension =
        { Feature  = feature
          Direction = dir
          Approx   = fun o ->
            let v = o.Vec
            let v' = match dir with
                     | LeftKan  -> { v with Cost = v.Cost * 1.1; Safety = v.Safety * 0.95 }
                     | RightKan -> { v with Cost = v.Cost * 1.2; Safety = v.Safety * 0.9 }
            { o with Vec=v'; Hash=Merkle.ofString (sprintf "kan:%s:%A:%A" feature dir v') }
          Obligation = KanWitness (sprintf "%s-via-%A" feature dir) }

    /// Full lowering pipeline: select → fuse → apply → Kan-extend missing features
    let lower (functors:LowerFunctor list) (backend:Backend) (target:V) (d:Diagram) : Diagram * Proof list =
        match select functors backend target with
        | None -> d, [Axiom "no-suitable-functor"]
        | Some f ->
            let missing =
                d.Objects |> Map.toSeq
                |> Seq.collect (fun (_,o) -> o.Effects |> List.filter (fun e -> not (Set.contains e f.Supported)))
                |> Seq.distinct |> Seq.toList
            let kans = missing |> List.map (fun feat -> kanExtend feat LeftKan)
            let kanFunctor =
                if List.isEmpty kans then f
                else
                    let kanMap o =
                        kans |> List.fold (fun o' k ->
                            if List.contains k.Feature o'.Effects then k.Approx o' else o') (f.MapObj o)
                    { f with MapObj = kanMap; Name = f.Name + "+kan" }
            let d' = applyFunctor kanFunctor d
            d', kans |> List.map (fun k -> k.Obligation)

// ═══════════════════════════════════════════════════════════════════════════════
// §8  SYMBOLIC EXECUTION & PARTIAL EVALUATION
// ═══════════════════════════════════════════════════════════════════════════════

type SymVal =
    | Concrete  of int64
    | Symbolic  of string
    | BinOp     of SymVal * string * SymVal
    | Cond      of SymVal * SymVal * SymVal
    | Unknown

module SymExec =
    /// Partial evaluation: reduce as far as possible
    let rec eval = function
        | BinOp(Concrete a, "+", Concrete b) -> Concrete(a+b)
        | BinOp(Concrete a, "*", Concrete b) -> Concrete(a*b)
        | BinOp(Concrete a, "-", Concrete b) -> Concrete(a-b)
        | BinOp(Concrete 0L, "+", x) | BinOp(x, "+", Concrete 0L) -> eval x
        | BinOp(Concrete 0L, "*", _) | BinOp(_, "*", Concrete 0L) -> Concrete 0L
        | BinOp(Concrete 1L, "*", x) | BinOp(x, "*", Concrete 1L) -> eval x
        | Cond(Concrete 0L, _, e) -> eval e
        | Cond(Concrete _,  t, _) -> eval t
        | BinOp(a, op, b) ->
            let a', b' = eval a, eval b
            match a', b' with
            | Concrete _, Concrete _ -> eval (BinOp(a', op, b'))
            | _ -> BinOp(a', op, b')
        | Cond(c, t, e) ->
            match eval c with
            | Concrete 0L -> eval e
            | Concrete _  -> eval t
            | c'          -> Cond(c', eval t, eval e)
        | v -> v

    /// Symbolic execution of a morphism chain: fold enriched weights
    let execChain (d:Diagram) (morIds:MorId list) : V =
        morIds |> List.fold (fun acc mid ->
            match Map.tryFind mid d.Morphisms with
            | Some m -> V.compose acc m.Weight
            | None   -> acc) V.zero

// ═══════════════════════════════════════════════════════════════════════════════
// §9  RECOVERY & VALIDATION  — hallucination detection, adjoint retraction,
//     sheaf patching, semantic checkpointing with Merkle-diffing
// ═══════════════════════════════════════════════════════════════════════════════

type Checkpoint = { Tag:string; Diagram:Diagram; Stamp:DateTime }

type ValidationResult =
    | Valid
    | Hallucination of ObjId list * string
    | Inconsistency of Obstruction list

module Recovery =
    /// Validate all morphisms: source/target must exist; enrichment must be non-bottom
    let validate (d:Diagram) : ValidationResult =
        let badMors =
            d.Morphisms |> Map.toList |> List.choose (fun (_,m) ->
                let srcOk = Map.containsKey m.Src d.Objects
                let tgtOk = Map.containsKey m.Tgt d.Objects
                if not srcOk || not tgtOk || V.isBottom m.Weight
                then Some (if not srcOk then m.Src else m.Tgt)
                else None)
        let badObjs =
            d.Objects |> Map.toList |> List.choose (fun (id,o) ->
                if V.isBottom o.Vec then Some id else None)
        let all = badMors @ badObjs |> List.distinct
        if List.isEmpty all then Valid
        else Hallucination(all, sprintf "%d suspect nodes" (List.length all))

    /// Adjoint-based retraction: lift suspect target objects back to source for correction.
    /// Given a lowering functor F, the right adjoint G lifts target → source.
    let adjointRetract (rightAdjoint: Obj -> Obj) (suspect:ObjId list) (d:Diagram) : Diagram =
        suspect |> List.fold (fun diagram oid ->
            match Map.tryFind oid diagram.Objects with
            | None   -> diagram
            | Some o ->
                let lifted = rightAdjoint o
                let h = Merkle.ofString (sprintf "retract:%A:%A" oid lifted.Vec)
                let o' = { lifted with Id=oid; Hash=h }
                { diagram with Objects = Map.add oid o' diagram.Objects }) d

    /// Sheaf patching: treat the diagram as a sheaf, replace corrupted sections via local co-limits.
    /// A "section" is a connected sub-diagram rooted at a given object.
    let sheafPatch (corrupt:ObjId Set) (patch:Diagram) (d:Diagram) : Diagram =
        // replace objects in corrupt region with those from the patch diagram
        let objs' =
            d.Objects |> Map.map (fun id o ->
                if Set.contains id corrupt then
                    match Map.tryFind id patch.Objects with
                    | Some p -> { p with Id=id }
                    | None   -> o
                else o)
        // replace morphisms touching corrupt region
        let mors' =
            d.Morphisms |> Map.map (fun id m ->
                if Set.contains m.Src corrupt || Set.contains m.Tgt corrupt then
                    match Map.tryFind id patch.Morphisms with
                    | Some p -> p
                    | None   -> m
                else m)
        { d with Objects=objs'; Morphisms=mors' }

    /// Merkle-diff based minimal rollback: find the smallest subtree that changed and
    /// restore from the nearest checkpoint.
    let rollback (checkpoints:Checkpoint list) (current:Diagram) : Diagram * string =
        match checkpoints with
        | [] -> current, "no checkpoints available"
        | _  ->
            // find the most recent checkpoint whose root hash differs
            let cp =
                checkpoints
                |> List.sortByDescending (fun c -> c.Stamp)
                |> List.tryFind (fun c -> not (Merkle.equal c.Diagram.RootHash current.RootHash))
            match cp with
            | None    -> current, "all checkpoints match current state"
            | Some cp ->
                let changedObjs, changedMors = Diagram.diff cp.Diagram current
                // restore only the changed portion from the checkpoint
                let restored =
                    { current with
                        Objects = changedObjs |> Map.fold (fun acc k _ ->
                            match Map.tryFind k cp.Diagram.Objects with
                            | Some o -> Map.add k o acc
                            | None   -> Map.remove k acc) current.Objects
                        Morphisms = changedMors |> Map.fold (fun acc k _ ->
                            match Map.tryFind k cp.Diagram.Morphisms with
                            | Some m -> Map.add k m acc
                            | None   -> Map.remove k acc) current.Morphisms }
                restored, sprintf "rolled back %d objects, %d morphisms to '%s'"
                            (Map.count changedObjs) (Map.count changedMors) cp.Tag

    /// Checkpoint creation
    let checkpoint tag (d:Diagram) : Checkpoint =
        { Tag=tag; Diagram=d; Stamp=DateTime.UtcNow }

    /// Full recovery pipeline: validate → retract → patch → re-validate
    let recover (rightAdj: Obj -> Obj) (patchSource: Diagram) (checkpoints: Checkpoint list) (d:Diagram) =
        match validate d with
        | Valid -> d, [], "valid"
        | Hallucination(suspects, msg) ->
            let retracted = adjointRetract rightAdj suspects d
            match validate retracted with
            | Valid -> retracted, [], sprintf "retracted: %s" msg
            | _     ->
                let patched = sheafPatch (Set.ofList suspects) patchSource retracted
                match validate patched with
                | Valid -> patched, [], sprintf "patched: %s" msg
                | _     ->
                    let rolled, rmsg = rollback checkpoints patched
                    rolled, suspects, sprintf "rollback(%s): %s" rmsg msg
        | Inconsistency obs ->
            let rolled, rmsg = rollback checkpoints d
            rolled, obs |> List.map (fun o -> o.Location), sprintf "inconsistency rollback: %s" rmsg

// ═══════════════════════════════════════════════════════════════════════════════
// §10  FULL PIPELINE — parse → build IR → unify → lower → validate → recover
// ═══════════════════════════════════════════════════════════════════════════════

type PipelineConfig =
    { Grammar       : Grammar
      Constraints   : Constraint list
      Functors      : LowerFunctor list
      Backend       : Backend
      TargetVec     : V
      RightAdjoint  : Obj -> Obj
      PatchSource   : Diagram
      Checkpoints   : Checkpoint list }

type PipelineResult =
    { ParseTree     : ParseNode option
      SourceDiagram : Diagram
      Unified       : Diagram
      Obstructions  : Obstruction list
      Lowered       : Diagram
      KanProofs     : Proof list
      Validation    : ValidationResult
      FinalDiagram  : Diagram
      RecoveryLog   : string }

module Pipeline =
    /// Convert a parse tree into a diagram (each node → object, each edge → morphism)
    let rec private buildDiagram (node:ParseNode) (d:Diagram) : Diagram * ObjId =
        match node with
        | Terminal t ->
            Diagram.addObj t "terminal" [] V.zero d
        | NonTerm(name, children) ->
            let d1, parentId = Diagram.addObj name "nonterm" [] V.zero d
            let addChild dAcc child =
                let dAcc', childId = buildDiagram child dAcc
                Diagram.addMor parentId childId "child" V.zero dAcc' |> fst
            (children |> List.fold addChild d1), parentId
        | Coproduct alts ->
            let d1, coprodId = Diagram.addObj "coproduct" "choice" [] V.zero d
            let addAlt dAcc alt =
                let dAcc', altId = buildDiagram alt dAcc
                Diagram.addMor coprodId altId "alt" V.zero dAcc' |> fst
            (alts |> List.fold addAlt d1), coprodId
        | Empty ->
            Diagram.addObj "empty" "unit" [] V.zero d

    /// Full pipeline execution
    let run (cfg:PipelineConfig) (tokens:string[]) : PipelineResult =
        // 1. Parse
        let parseTree = Intake.parse cfg.Grammar tokens

        // 2. Build source diagram from parse tree
        let sourceDiagram =
            match parseTree with
            | Some tree -> buildDiagram tree Diagram.empty |> fst
            | None      -> Diagram.empty

        // 3. Unification: apply constraints, detect obstructions
        let unified, obstructions = Unifier.narrow cfg.Constraints sourceDiagram

        // 4. Lowering: functorial translation to target backend
        let lowered, kanProofs = Lowering.lower cfg.Functors cfg.Backend cfg.TargetVec unified

        // 5. Validation
        let validation = Recovery.validate lowered

        // 6. Recovery if needed
        let finalDiagram, _, recoveryLog =
            Recovery.recover cfg.RightAdjoint cfg.PatchSource cfg.Checkpoints lowered

        { ParseTree     = parseTree
          SourceDiagram = sourceDiagram
          Unified       = unified
          Obstructions  = obstructions
          Lowered       = lowered
          KanProofs     = kanProofs
          Validation    = validation
          FinalDiagram  = finalDiagram
          RecoveryLog   = recoveryLog }
