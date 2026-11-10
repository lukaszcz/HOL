(* Ordinary-source observations only. No graph constants, materialisation,
   semantic graph equality decisions, or proof authority live here.

   Operands are shared, never copied into a native template. Constructors do
   only local work (from_template validates its hole/operand lists). Private
   binding is lazy; queries lower it with charged, query-local DAG memos.
   Callers admit retained native templates and account for construction work;
   observation callbacks account for expansion and query traversals.
   Template holes are variables. Binders must be fresh for actual source
   operands, not merely holes, EXCEPT when a hole models an original lexical
   body: its source binder descriptor is intentionally captured by the same
   template binder (for example, a comprehension body).

   The sole global state is an unbounded identity supply: no syntax, term,
   observation cache, or invocation state is retained by it. Query caches are
   local and keyed by these identities, not by structural term equality. *)
structure SmtLib_ConstructorSyntax :> SmtLib_ConstructorSyntax =
struct
  val ERR = Feedback.mk_HOL_ERR "SmtLib_ConstructorSyntax"
  val serial = ref (0 : IntInf.int)

  (* Select the public opening convention, not a kernel/configuration name.
     Some kernels freshen even a differently typed free namesake; others
     expose the stored binder unchanged. Retain only the probe's boolean,
     never its tiny native terms. No source operand is used by this probe. *)
  val opening_freshens_names =
    let
      val binder = Term.mk_var ("smt_constructor_open_probe", Type.bool)
      val namesake = Term.mk_var ("smt_constructor_open_probe",
                                 Type.--> (Type.bool, Type.bool))
      val (opened, _) = Term.dest_abs (Term.mk_abs (binder, namesake))
    in not (Term.aconv binder opened) end

  datatype syntax = Syntax of
    {id : IntInf.int, ty : Type.hol_type, node : node,
     private_bindings : bool}
  and node =
      Native of Term.term
    | Private of Term.term
    | Template of {template : Term.term, holes : Term.term list,
                   operands : syntax list, avoids : Term.term list option}
    | Application of syntax * syntax
    | Abstraction of Term.term * Term.term * syntax
    | PrivateBinding of Term.term * syntax
    (* Simultaneous FREE-variable renaming. Unlike rebuilding named lambdas,
       this preserves stored inner binder names even on a name collision.
       It describes the de Bruijn opening performed by ordinary dest_abs. *)
    | Renaming of syntax * (Term.term * Term.term) list

  fun has_private_bindings (Syntax {private_bindings, ...}) =
    private_bindings
  fun make ty node =
    let
      val id = !serial
      val private_bindings = case node of
          PrivateBinding _ => true
        | Application (f,x) => has_private_bindings f orelse
                               has_private_bindings x
        | Abstraction (_,_,body) => has_private_bindings body
        | Renaming (body,_) => has_private_bindings body
        | Template {operands,...} => List.exists has_private_bindings operands
        | _ => false
    in
      serial := id + 1;
      Syntax {id=id, ty=ty, node=node, private_bindings=private_bindings}
    end
  datatype view = Variable of Term.term | Atom of Term.term
                | Apply of syntax * syntax
                | Abstract of Term.term * syntax

  fun identity (Syntax {id, ...}) = id
  fun type_of (Syntax {ty, ...}) = ty
  fun private_atom term = make (Term.type_of term) (Private term)
  fun native term = make (Term.type_of term) (Native term)
  val variable = native
  fun application (operator, operand) =
    make (#2 (Type.dom_rng (type_of operator)))
      (Application (operator, operand))
  fun abstraction (variable, body) =
    if Term.is_var variable then
      make (Type.--> (Term.type_of variable, type_of body))
        (Abstraction (variable, variable, body))
    else raise ERR "abstraction" "binder is not a variable"
  fun renaming (body, []) = body
    | renaming (body, replacements) =
        make (type_of body) (Renaming (body, replacements))

  (* all_atomsl visits the STORED binder first, including on a closure.
     A seeded comparator intercepts that first insertion, without walking
     the body or depending on dest_abs's potentially freshened binder name.
     See also the ordinary-kernel importer's binder probe. *)
  fun stored_binder (observe : IntInf.int -> unit) term =
    let
      exception Binder of Term.term
      val _ = observe 1
      val seed = Term.mk_var ("smt_constructor_binder_probe", Type.bool)
      fun capture (left, right) =
        (observe 1; raise Binder
          (if Portable.pointer_eq (left, seed) then right else left))
    in
      (ignore (Term.all_atomsl [term]
         (HOLset.add (HOLset.empty capture, seed)));
       raise ERR "stored_binder" "abstraction without binder")
      handle Binder variable => variable
    end

  fun from_template_mode avoids {template, holes, operands} =
    let
      fun validate ([], []) = ()
        | validate (hole :: hs, _ :: os) =
            if Term.is_var hole then validate (hs, os)
            else raise ERR "from_template" "hole is not a variable"
        | validate _ = raise ERR "from_template" "hole/operand arity"
      val _ = validate (holes, operands)
    in make (Term.type_of template) (Template
      {template=template,holes=holes,operands=operands,avoids=avoids}) end
  val from_template = from_template_mode NONE

  (* pairSyntax.mk_anylet on ordinary (variable) SMT-LIB bindings builds
       LET (... (LET (\\v1 ... vn. body) rhs1) ...) rhsn
     not nested unary let bodies and not beta-redex applications. *)
  fun let_expression ([], _) =
        raise ERR "let_expression" "no binding"
    | let_expression (bindings, body) =
        let
          val function = List.foldr
            (fn ((variable, _), rest) => abstraction (variable, rest))
            body bindings
          fun bind ((_, rhs), function) =
            let
              val (domain, range) = Type.dom_rng (type_of function)
              val arrow = Type.-->
              val constant = Term.mk_thy_const
                {Thy = "bool", Name = "LET",
                 Ty = arrow (arrow (domain, range), arrow (domain, range))}
            in application (application (native constant, function), rhs) end
        in List.foldl bind function bindings end

  fun dictionary (observe : IntInf.int -> unit) =
    Redblackmap.mkDict
      (fn (left, right) => (observe 1; IntInf.compare (left, right)))
  fun type_work (observe : IntInf.int -> unit) ty =
    (observe 1;
     if Type.is_vartype ty then
       observe (IntInf.fromInt (String.size (Type.dest_vartype ty)))
     else
       let val {Thy, Tyop, Args} = Type.dest_thy_type ty
           val _ = observe (IntInf.fromInt
             (String.size Thy + String.size Tyop))
       in List.app (type_work observe) Args end)

  fun same_variable (observe : IntInf.int -> unit) (left, right) =
    let
      val _ = observe 1
      val (left_name, left_type) = Term.dest_var left
      val (right_name, right_type) = Term.dest_var right
      val _ = observe (IntInf.fromInt
        (String.size left_name + String.size right_name))
    in
      left_name = right_name andalso
      (type_work observe left_type; type_work observe right_type;
       Type.compare (left_type, right_type) = EQUAL)
    end

  (* Expand only an admitted native template, never actual operands.
     Expansion is query-local; the query's source-identity memo shares its
     result without retaining an expanded syntax tree between queries. *)
  fun expand_template_mode lexical (observe : IntInf.int -> unit)
        {template, holes, operands, avoids} =
    let
      fun bindings ([], []) = (observe 1; [])
        | bindings (hole :: hs, operand :: os) =
            (observe 1; (hole, operand) :: bindings (hs, os))
        | bindings _ = raise ERR "from_template" "hole/operand arity"
      fun lookup _ [] = (observe 1; NONE)
        | lookup term ((variable, value) :: rest) =
            (observe 1;
             if same_variable observe (term, variable) then SOME value
             else lookup term rest)
      val avoids = ref avoids
      fun marker stored = case !avoids of NONE => stored
        | SOME variables =>
          let
            val bytes = List.foldl (fn (variable,total) =>
              (observe 1;total + 1 + IntInf.fromInt
                (String.size (#1 (Term.dest_var variable))))) 0 variables
            val fresh = Term.variant variables stored
            val size = IntInf.fromInt
              (String.size (#1 (Term.dest_var fresh)))
            val original = IntInf.fromInt
              (String.size (#1 (Term.dest_var stored)))
            val _ = observe ((size-original+1)*(bytes+size+1))
            val _ = avoids := SOME (fresh::variables)
          in fresh end
      fun walk environment term =
        (observe 1;
         if Term.is_var term then
           (case lookup term environment of
              SOME operand => operand
            | NONE => if lexical then native term else private_atom term)
         else if Term.is_comb term then
           let val (operator, operand) = Term.dest_comb term
           in application (walk environment operator,
                           walk environment operand) end
         else if Term.is_abs term then
           let
             val stored = stored_binder observe term
             val (opened, body) = Term.dest_abs term
             (* Restore the template's stored binder, rather than adopting
                a fresh name caused just by the template's hole names. This
                entry also masks a hole shadowed by the template binder. *)
             val marker = marker stored
             val environment = (opened, native marker) :: environment
           in make (Term.type_of term)
                (Abstraction (stored,marker,walk environment body)) end
         else native term)
    in walk (bindings (holes, operands)) template end
  (* Ordinary template free variables remain lexical. Private provenance
     must be supplied explicitly by private_atom operands at template holes. *)
  fun expand_template observe source =
    expand_template_mode true observe source

  (* Keep lexical free occurrences, stored binders, and private atom names
     distinct. A binder or renaming acts only on lexical free occurrences;
     private names still participate in all_variables freshness queries.
     First-occurrence order is retained so all_variables also reproduces
     the ordinary all_varsl list order, not just its set of variables. *)
  datatype occurrence = Free of Term.term | Bound of Term.term
                      | Opaque of Term.term
  fun variable_of (Free variable) = variable
    | variable_of (Bound variable) = variable
    | variable_of (Opaque variable) = variable
  fun same_occurrence observe (Free left, Free right) =
        same_variable observe (left, right)
    | same_occurrence observe (Bound left, Bound right) =
        same_variable observe (left, right)
    | same_occurrence observe (Opaque left, Opaque right) =
        same_variable observe (left, right)
    | same_occurrence observe _ = (observe 1; false)

  fun member equal value [] = false
    | member equal value (head :: rest) =
        equal (value, head) orelse member equal value rest

  fun unique (observe : IntInf.int -> unit) equal entries =
    let
      fun loop [] result = (observe 1; List.rev result)
        | loop (entry :: rest) result =
            (observe 1;
             loop rest (if member equal entry result then result
                        else entry :: result))
    in loop entries [] end

  fun free_occurrences (observe : IntInf.int -> unit) entries =
    List.foldr (fn (Free variable, rest) =>
                       (observe 1; variable :: rest)
                 | (_, rest) => (observe 1; rest)) [] entries

  fun replace observe replacements variable =
    let
      fun find [] = (observe 1; variable)
        | find ((old, replacement) :: rest) =
            if same_variable observe (old, variable) then replacement
            else find rest
    in find replacements end

  (* Lower explicit private binding only for an observation. Collect raw
     names (including hidden lexical markers and renaming domains/ranges)
     once, expanding each template once. Fresh names are indexed, not found
     by repeatedly scanning a growing avoids list. No compound native term
     is constructed. The second memo is indexed by source identity and ONLY
     relevant private bindings, so unrelated scopes cannot unshare a DAG.

     Adjacent private binders are lowered as one batch: neither freshness
     nor replacement walks their common suffix once per binder. All caches,
     expanded templates, and callbacks die with this reader. *)
  fun private_reader observe =
    let
      val resolved = ref (dictionary observe)
      fun lower root =
        let
          fun compare_name (a,b) =
            (observe (1 + IntInf.fromInt (String.size a + String.size b));
             String.compare (a,b))
          fun compare_variable (a,b) =
            let val (x,xty) = Term.dest_var a
                val (y,yty) = Term.dest_var b
                val _ = observe
                  (1 + IntInf.fromInt (String.size x + String.size y))
                val _ = type_work observe xty
                val _ = type_work observe yty
            in Term.compare (a,b) end
          val empty = Redblackset.empty compare_variable
          val names = ref (Redblackset.empty compare_name)
          val dependencies = ref (dictionary observe)
          val expansions = ref (dictionary observe)
          val pending = ref []
          val markers = ref (dictionary observe)
          fun avoid variable =
            (observe 1;
             if Term.is_var variable then
               names := Redblackset.add (!names,#1 (Term.dest_var variable))
             else ())
          fun native_names term =
            (observe 1;
             if Term.is_var term then avoid term
             else if Term.is_comb term then
               let val (f,x) = Term.dest_comb term
               in native_names f; native_names x end
             else if Term.is_abs term then
               (avoid (stored_binder observe term);
                native_names (#2 (Term.dest_abs term)))
             else ())
          fun union (left,right) = Redblackset.foldl
            (fn (variable,rest) =>
              (observe 1; Redblackset.add (rest,variable))) left right
          fun collect (Syntax {id,node,...}) =
            (observe 1;
             case Redblackmap.peek (!dependencies,id) of
               SOME result => result
             | NONE =>
               let
                 val result = case node of
                     Native term => (native_names term; empty)
                   | Private term =>
                       (avoid term;
                        if Term.is_var term then Redblackset.add (empty,term)
                        else empty)
                   | Template template =>
                       let val expanded = expand_template observe template
                           val _ = observe 1
                           val _ = expansions :=
                             Redblackmap.insert (!expansions,id,expanded)
                       in collect expanded end
                   | Application (f,x) => union (collect f,collect x)
                   | Abstraction (stored,marker,body) =>
                       (avoid stored; avoid marker; collect body)
                   | Renaming (body,replacements) =>
                       (List.app (fn (old,value) =>
                          (avoid old; avoid value)) replacements;
                        collect body)
                   | PrivateBinding (descriptor,body) =>
                       let
                         val _ = avoid descriptor
                         val result = collect body
                         val _ = pending := (id,descriptor) :: !pending
                       in
                         if Redblackset.member (result,descriptor) then
                           Redblackset.delete (result,descriptor)
                         else result
                       end
                 val _ = observe 1
                 val _ = dependencies :=
                   Redblackmap.insert (!dependencies,id,result)
               in result end)
          val _ = collect root
          fun allocate (id,descriptor) =
            let
              (* Identity only selects a candidate. Even adversarial lexical
                 names are checked; different types cannot evade freshness. *)
              val base = "smt_private_" ^ IntInf.toString id
              fun fresh name =
                (observe (1 + IntInf.fromInt (String.size name));
                 if Redblackset.member (!names,name) then fresh (name ^ "'")
                 else name)
              val name = fresh base
              val _ = names := Redblackset.add (!names,name)
              val marker = Term.mk_var (name,Term.type_of descriptor)
              val _ = observe 1
            in markers := Redblackmap.insert (!markers,id,marker) end
          val _ = List.app allocate (!pending)
          fun compare_id (a,b) = (observe 1; IntInf.compare (a,b))
          val memo = ref (Redblackmap.mkDict
            (fn ((a,xs),(b,ys)) => case compare_id (a,b) of
                EQUAL => List.collate compare_id (xs,ys) | order => order))
          fun marker id =
            (observe 1; Redblackmap.find (!markers,id))
          (* Batch suffixes retain persistent environments without eagerly
             projecting every growing suffix dependency set. Compare only
             when another incoming edge actually requests that suffix. *)
          val batches = ref (dictionary observe)
          fun same_environment relevant (left,right) =
            Redblackset.foldl (fn (variable,result) =>
              (observe 1;
               result andalso
               (case (Redblackmap.peek (left,variable),
                      Redblackmap.peek (right,variable)) of
                  (NONE,NONE) => true
                | (SOME (a,_),SOME (b,_)) => compare_id (a,b)=EQUAL
                | _ => false))) true relevant
          fun finish prefix body = List.foldl
            (fn ((id,ty,binder,environment),inner) =>
              let
                val _ = observe 1
                val result = make ty (Abstraction (binder,binder,inner))
                val bucket = case Redblackmap.peek (!batches,id) of
                    NONE => [] | SOME bucket => bucket
                val _ = observe 1
                val _ = batches := Redblackmap.insert
                  (!batches,id,(environment,result)::bucket)
              in result end) body prefix
          fun walk environment (source as Syntax {id,ty,node,...}) =
            let
              val _ = observe 1
              val relevant = Redblackmap.find (!dependencies,id)
              val (environment,ids) = Redblackset.foldl
                (fn (variable,(bindings,ids)) =>
                  (observe 1;
                   case Redblackmap.peek (environment,variable) of
                     NONE => (bindings,ids)
                   | SOME (id,value) =>
                       (Redblackmap.insert (bindings,variable,(id,value)),
                        id::ids)))
                (Redblackmap.mkDict compare_variable,[]) relevant
              val key = (id,ids)
            in
              case Redblackmap.peek (!memo,key) of SOME result => result
              | NONE =>
                let
                  fun batch bindings prefix
                        (Syntax {id,ty,node=PrivateBinding (variable,body),
                                 ...}) =
                        let
                          val _ = observe 1
                          val bucket = case Redblackmap.peek (!batches,id) of
                              NONE => [] | SOME bucket => bucket
                          val cached = List.find (fn (other,_) =>
                            (observe 1;
                             same_environment
                               (Redblackmap.find (!dependencies,id))
                               (bindings,other))) bucket
                        in case cached of
                            SOME (_,result) => finish prefix result
                          | NONE =>
                            let
                              val binder = marker id
                              val extended = Redblackmap.insert
                                (bindings,variable,(id,native binder))
                            in batch extended
                              ((id,ty,binder,bindings)::prefix) body end
                        end
                    | batch bindings prefix body =
                        finish prefix (walk bindings body)
                  val result = case node of
                      Native _ => source
                    | Private term =>
                        if Term.is_var term then
                          (case Redblackmap.peek (environment,term) of
                             SOME (_,value) => value | NONE => source)
                        else source
                    | Template _ => walk environment
                        (Redblackmap.find (!expansions,id))
                    | Application (f,x) =>
                        application (walk environment f,walk environment x)
                    | Abstraction (stored,binder,body) => make ty
                        (Abstraction (stored,binder,walk environment body))
                    | Renaming (body,replacements) =>
                        renaming (walk environment body,replacements)
                    | PrivateBinding _ => batch environment [] source
                  val _ = observe 1
                  val _ = memo := Redblackmap.insert (!memo,key,result)
                in result end
            end
        in walk (Redblackmap.mkDict compare_variable) root end
      fun resolve (source as Syntax {id,...}) =
        (observe 1;
         if not (has_private_bindings source) then source
         else case Redblackmap.peek (!resolved,id) of
             SOME result => result
           | NONE =>
               let val result = lower source
                   val _ = observe 1
                   val _ = resolved :=
                     Redblackmap.insert (!resolved,id,result)
               in result end)
    in resolve end

  (* Open only retained native source syntax with the public dest_abs.
     Its exposed binder may be freshened: remove its FREE occurrences, but
     retain all stored inner binders and record the original stored binder.
     This preserves exact all_varsl names and order, not just alpha-equivalence.
     No native term is assembled from synthetic operands by this visitor. *)
  fun observations observe =
    let
      val resolve = private_reader observe
      val memo = ref (dictionary observe)
      fun merge (left, right) =
        (observe (IntInf.fromInt (List.length left));
         unique observe (same_occurrence observe) (left @ right))
      fun native_variables term =
        (observe 1;
         if Term.is_var term then [Free term]
         else if Term.is_comb term then
           let val (operator, operand) = Term.dest_comb term
           in merge (native_variables operator, native_variables operand) end
         else if Term.is_abs term then
           let
             val stored = stored_binder observe term
             val (opened, body) = Term.dest_abs term
             val entries = List.filter
               (fn Free variable =>
                     not (same_variable observe (opened, variable))
                 | _ => (observe 1; true)) (native_variables body)
           in merge ([Bound stored], entries) end
         else [])
      fun visit (source as Syntax {id, node, ...}) =
        (observe 1;
         case Redblackmap.peek (!memo, id) of
           SOME entries => entries
         | NONE =>
           let
             val entries =
               case node of
                 Native term => native_variables term
               | Private term => [Opaque term]
               | PrivateBinding _ => visit (resolve source)
               | Template source => visit (expand_template observe source)
               | Application (operator, operand) =>
                   merge (visit operator, visit operand)
               | Abstraction (stored, binder, body) =>
                   let
                     val entries = List.filter
                       (fn Free variable =>
                             not (same_variable observe (binder, variable))
                         | _ => (observe 1; true)) (visit body)
                   in merge ([Bound stored], entries) end
               | Renaming (body, replacements) =>
                   unique observe (same_occurrence observe)
                     (List.map
                       (fn Free variable =>
                             (observe 1;
                              Free (replace observe replacements variable))
                         | entry => (observe 1; entry)) (visit body))
             val _ = observe 1
             val _ = memo := Redblackmap.insert (!memo, id, entries)
           in entries end)
    in fn source => visit (resolve source) end

  (* Construction never inspects the body or retains the charging callback. *)
  fun private_abstraction observe (descriptor, body) =
    (observe 1;
     if Term.is_var descriptor then
       make (Type.--> (Term.type_of descriptor, type_of body))
         (PrivateBinding (descriptor,body))
     else raise ERR "private_abstraction" "binder is not a variable")

  fun contains_constant observe {Thy, Name} root =
    let
      val memo = ref (dictionary observe)
      fun native_contains term =
        (observe 1;
         if Term.is_const term then
           let val actual = Term.dest_thy_const term
               val _ = observe (IntInf.fromInt
                 (String.size Thy + String.size Name +
                  String.size (#Thy actual) + String.size (#Name actual)))
           in #Thy actual = Thy andalso #Name actual = Name end
         else if Term.is_comb term then
           let val (operator, operand) = Term.dest_comb term
           in native_contains operator orelse native_contains operand end
         else if Term.is_abs term then
           native_contains (#2 (Term.dest_abs term))
         else false)
      fun visit (Syntax {id, node, ...}) =
        (observe 1;
         case Redblackmap.peek (!memo, id) of
           SOME result => result
         | NONE =>
           let
             val result =
               case node of
                 Native term => native_contains term
               | Private _ => false
               | Template source => visit (expand_template observe source)
               | Application (operator, operand) =>
                   visit operator orelse visit operand
               | Abstraction (_, _, body) => visit body
               | PrivateBinding (_,body) => visit body
               | Renaming (body, _) => visit body
             val _ = observe 1
             val _ = memo := Redblackmap.insert (!memo, id, result)
           in result end)
    in visit root end

  fun all_variables observe roots =
    let
      val entries = observations observe
      val equal = same_variable observe
      fun insert variable variables =
        if member equal variable variables then variables
        else variable :: variables
      fun variables root =
        List.foldl (fn (entry, rest) =>
          (observe 1; insert (variable_of entry) rest)) [] (entries root)
      (* These empty-list cases matter: Portable.union returns the other
         list verbatim, otherwise it inserts the left list left-to-right. *)
      fun union ([], right) = (observe 1; right)
        | union (left, []) = (observe 1; left)
        | union (head :: rest, right) =
            (observe 1; union (rest, insert head right))
    in List.foldr (fn (root, rest) =>
         (observe 1; union (variables root, rest))) [] roots end

  fun free_variables observe syntax =
    free_occurrences observe (observations observe syntax)

  (* Qualified-head replay supplies fresh, distinct holes. On an opening-
     freshening kernel substitution preserves stored binder names; on a
     name-carrying kernel it must rename them to avoid introduced FREE
     names, even at a different type. Do not confuse these native names
     with the internal lexical markers representing metadata binding.
     Only the admitted template is rebuilt as metadata; operands stay
     shared and are inspected through charged variable queries only. *)
  fun from_substitution observe (source as {template,holes,operands}) =
    if opening_freshens_names then
      from_template_mode
        (SOME (holes @ all_variables observe (native template :: operands)))
        source
    else
      let
        val entries = observations observe
        fun free syntax = free_occurrences observe (entries syntax)
        val equal = same_variable observe
        (* The last field distinguishes actual substitutions (including
           outer binder renamings) from unchanged lexical bindings. Only
           actual substitutions introduce names at an inner abstraction. *)
        fun bindings ([], []) = (observe 1; [])
          | bindings (hole :: hs, operand :: os) =
              (observe 1;
               if Term.is_var hole then
                 (hole, operand, free operand, true) :: bindings (hs, os)
               else raise ERR "from_template" "hole is not a variable")
          | bindings _ = raise ERR "from_template" "hole/operand arity"
        val environment = bindings (holes, operands)
        val markers = ref
          (holes @ all_variables observe (native template :: operands))
        fun fresh avoids variable =
          let
            val bytes = List.foldl (fn (avoid, total) =>
              (observe 1; total + 1 + IntInf.fromInt
                (String.size (#1 (Term.dest_var avoid))))) 0 avoids
            (* Native substitution varies names without consulting the
               theory's constant names, unlike Term.variant. *)
            val result = Term.prim_variant avoids variable
            val size = IntInf.fromInt
              (String.size (#1 (Term.dest_var result)))
            val original = IntInf.fromInt
              (String.size (#1 (Term.dest_var variable)))
            val _ = observe ((size-original+1)*(bytes+size+1))
          in result end
        fun lookup variable [] = (observe 1; native variable)
          | lookup variable ((old, value, _, _) :: rest) =
              if equal (variable, old) then value else lookup variable rest
        fun walk environment term =
          (observe 1;
           if Term.is_var term then lookup term environment
           else if Term.is_comb term then
             let val (operator, operand) = Term.dest_comb term
             in application (walk environment operator,
                             walk environment operand) end
           else if Term.is_abs term then
             let
               val (stored, body) = Term.dest_abs term
               val environment = List.filter
                 (fn (old, _, _, _) => not (equal (stored, old))) environment
               val current = free (native term)
               val introduced = List.foldl
                 (fn ((old, _, variables, active), rest) =>
                   (observe 1;
                    if active andalso member equal old current then
                      (observe (IntInf.fromInt (List.length variables));
                       variables @ rest)
                    else rest)) [] environment
               val name = #1 (Term.dest_var stored)
               fun clashes variable =
                 let val other = #1 (Term.dest_var variable)
                     val _ = observe (1 + IntInf.fromInt
                       (String.size name + String.size other))
                 in name = other end
               val changed = List.exists clashes introduced
               (* Native substitution avoids the ORIGINAL body free names
                  as well, including holes and the old bound variable.
                  Bound names inside operands do not participate. *)
               val binder = if changed then
                   (observe (IntInf.fromInt (List.length introduced));
                    fresh (introduced @ free (native body)) stored)
                 else stored
               val marker = fresh (!markers) stored
               val _ = markers := marker :: !markers
               val environment =
                 (stored, native marker, [binder], changed) :: environment
             in make (Term.type_of term)
                  (Abstraction (binder, marker, walk environment body)) end
           else native term)
      in walk environment template end

  fun retained_native observe root =
    let
      fun head (Syntax {node,...}) =
        (observe 1;case node of
           Native term => SOME (term,true)
         | Private term => SOME (term,false)
         | Template source => head (expand_template observe source)
         | Renaming (body,replacements) =>
             (case head body of SOME (term,lexical) =>
                if Term.is_var term then
                  SOME (if lexical then replace observe replacements term
                        else term, lexical)
                else if Term.is_const term then SOME (term,lexical)
                else NONE
              | NONE => NONE)
         | _ => NONE)
    in Option.map #1 (head root) end

  fun is_numeric_literal observe root =
    let
      fun unfold (whole as Syntax {node,...}) =
        (observe 1;case node of
           Template source => unfold (expand_template observe source)
         | Renaming (body,_) => unfold body
         | Native term => if Term.is_comb term then
             let val (f,x) = Term.dest_comb term
             in application (native f,native x) end else whole
         | _ => whole)
      fun constant expected source =
        case unfold source of Syntax {node=Native term,...} =>
          Term.is_const term andalso Term.same_const term expected
        | _ => false
      fun unary expected source =
        case unfold source of Syntax {node=Application (f,x),...} =>
          if constant expected f then SOME x else NONE
        | _ => NONE
      fun bits source = constant numSyntax.alt_zero_tm source orelse
        (case unary numSyntax.bit1_tm source of SOME rest => bits rest
         | NONE => case unary numSyntax.bit2_tm source of
             SOME rest => bits rest | NONE => false)
      fun natural source = constant numSyntax.zero_tm source orelse
        (case unary numSyntax.numeral_tm source of
           SOME rest => bits rest | NONE => false)
      fun integer source =
        case unary intSyntax.negate_tm source of
          SOME rest => integer rest
        | NONE => case unary intSyntax.int_injection source of
            SOME rest => natural rest | NONE => false
    in natural root orelse integer root end

  fun is_constant observe constant root =
    let
      fun head (Syntax {node,...}) =
        (observe 1;case node of
           Native term => Term.is_const term andalso
             Term.same_const term constant
         | Template source => head (expand_template observe source)
         | Renaming (body,_) => head body
         | _ => false)
    in head root end

  fun abstraction_reader observe =
    let
      val resolve = private_reader observe
      val entries = observations observe
      val heads = ref (dictionary observe)
      fun free body = free_occurrences observe (entries body)
      fun without variable variables = List.filter
        (fn other => not (same_variable observe (variable, other))) variables
      fun renamed (body, replacements) =
        (observe (1 + IntInf.fromInt (List.length replacements));
         renaming (body, replacements))
      fun fresh avoids variable =
        let
          val bytes = List.foldl (fn (avoid, total) =>
            (observe 1; total + 1 + IntInf.fromInt
              (String.size (#1 (Term.dest_var avoid))))) 0 avoids
          val result = Term.variant avoids variable
          val size = IntInf.fromInt
            (String.size (#1 (Term.dest_var result)))
          val original = IntInf.fromInt
            (String.size (#1 (Term.dest_var variable)))
          (* Account for the native name-only candidate search as well. *)
          val _ = observe ((size - original + 1) * (bytes + size + 1))
        in result end
      (* Charge native destructor work as well as the metadata head visit.
         The stock dest_abs traverses/rebuilds this native fragment; it
         never receives a term containing synthetic source operands. *)
      fun native_work term =
        (observe 1;
         if Term.is_comb term then
           let val (operator, operand) = Term.dest_comb term
           in native_work operator; native_work operand end
         else if Term.is_abs term then
           native_work (#2 (Term.dest_abs term))
         else ())
      (* stored name, exposed bound-occurrence marker, unbound body.
         Markers distinguish binding from free-variable renamings whose
         range might otherwise capture a stored inner binder name. *)
      fun head (syntax as Syntax {id, node, ...}) =
        (observe 1;
         case Redblackmap.peek (!heads, id) of
           SOME result => result
         | NONE =>
           let
             val result =
               case node of
                 Application _ => NONE
               | Private _ => NONE
               | PrivateBinding _ => head (resolve syntax)
               | Template source => head (expand_template observe source)
               | Abstraction (stored, marker, body) =>
                   SOME (stored, marker, body)
               | Native term =>
                   if not (Term.is_abs term) then NONE
                   else
                     let
                       val stored = stored_binder observe term
                       val _ = native_work term
                       (* Only the freshening convention needs an internal
                          lexical marker to avoid dest_abs's clash/retry path.
                          On a name-carrying kernel rename_bvar can itself
                          rename inner binders: open directly instead. *)
                       val opened_term = if opening_freshens_names then
                           Term.rename_bvar (#1 (Term.dest_var
                             (fresh (stored :: free syntax) stored))) term
                         else term
                       val (opened, body) = Term.dest_abs opened_term
                       val _ = observe 1
                     in SOME (stored, opened, native body) end
               | Renaming (body, replacements) =>
                   (case head body of
                      NONE => NONE
                    | SOME (stored, marker, inner) =>
                      let
                        val remaining = List.filter
                          (fn (old, _) =>
                            not (same_variable observe (old, marker)))
                          replacements
                        val avoids = List.foldl
                          (fn ((old, value), rest) =>
                            (observe 1; old :: value :: rest))
                          (marker :: free inner) remaining
                        val new_marker = fresh avoids marker
                        val inner = renamed
                          (inner, (marker, new_marker) :: remaining)
                      in SOME (stored, new_marker, inner) end)
             val _ = observe 1
             val _ = heads := Redblackmap.insert (!heads, id, result)
           in result end)
      fun expose syntax =
        (observe 1;
         case head syntax of
           NONE => NONE
         | SOME (stored, marker, body) =>
           let
             val avoids = without marker (free body)
             val name = #1 (Term.dest_var stored)
             fun clashes variable =
               let val other = #1 (Term.dest_var variable)
                   val _ = observe (1 + IntInf.fromInt
                     (String.size name + String.size other))
               in name = other end
             val binder = if opening_freshens_names andalso
                             List.exists clashes avoids
                          then fresh avoids stored else stored
             val body = if same_variable observe (marker, binder) then body
                        else renamed (body, [(marker, binder)])
           in SOME (binder,body) end)
    in fn source => expose (resolve source) end

  fun dest_abs observe root = abstraction_reader observe root
  fun strip_abs observe root =
    let val expose = abstraction_reader observe
        fun peel syntax prefix = case expose syntax of
            NONE => (List.rev prefix,syntax)
          | SOME (binder,body) => peel body (binder::prefix)
    in peel root [] end

  (* One observation-local reader retains expanded heads and children.
     Native and template free variables remain lexical; only explicit
     private atoms are opaque. Renaming preserves provenance at each leaf. *)
  fun view_reader observe =
    let
      val resolve = private_reader observe
      val memo = ref (dictionary observe)
      val expose = abstraction_reader observe
      fun abstract source = case expose source of
          SOME pair => Abstract pair
        | NONE => raise ERR "view" "missing abstraction"
      fun visit (source as Syntax {id,node,...}) =
        (observe 1;
         case Redblackmap.peek (!memo,id) of SOME result => result
         | NONE =>
           let
             val result = case node of
                 Private term => Atom term
               | PrivateBinding _ => visit (resolve source)
               | Native term =>
                   if Term.is_var term then Variable term
                   else if Term.is_comb term then
                     let val (f,x) = Term.dest_comb term
                     in Apply (native f,native x) end
                   else if Term.is_abs term then abstract source
                   else Atom term
               | Application pair => Apply pair
               | Abstraction _ => abstract source
               | Template template => visit (expand_template observe template)
               | Renaming (body,replacements) =>
                   (case visit body of
                      Variable term =>
                        Variable (replace observe replacements term)
                    | Atom term => Atom term
                    | Apply (f,x) =>
                        (observe (2 * IntInf.fromInt
                          (List.length replacements));
                         Apply (renaming (f,replacements),
                                renaming (x,replacements)))
                    | Abstract _ => abstract source)
             val _ = observe 1
             val _ = memo := Redblackmap.insert (!memo,id,result)
           in result end)
    in fn source => visit (resolve source) end

  fun view observe source = view_reader observe source
  fun dest_comb observe source = case view observe source of
      Apply pair => SOME pair | _ => NONE

  (* Ordinary source alpha comparison, never semantic graph equality.
     The memo includes only binders relevant to either shared child;
     unrelated enclosing binders cannot duplicate a shared suffix walk. *)
  fun aconv observe (left,right) =
    let
      val read = view_reader observe
      val entries = observations observe
      fun free source = free_occurrences observe (entries source)
      val equal = same_variable observe
      val serial = ref (0 : IntInf.int)
      fun compare_id (a,b) = (observe 1; IntInf.compare (a,b))
      val memo = ref (Redblackmap.mkDict
        (fn ((a,b,xs),(c,d,ys)) =>
          case compare_id (a,c) of EQUAL =>
            (case compare_id (b,d) of EQUAL =>
               List.collate compare_id (xs,ys) | order => order)
          | order => order))
      fun lookup select variable [] = (observe 1; NONE)
        | lookup select variable ((a,b,id)::rest) =
            if equal (variable,select (a,b)) then SOME id
            else lookup select variable rest
      fun variables environment (a,b) =
        case (lookup #1 a environment,lookup #2 b environment) of
          (NONE,NONE) => equal (a,b)
        | (SOME x,SOME y) => (observe 1; x=y)
        | _ => false
      fun atom (a,b) =
        if Term.is_var a andalso Term.is_var b then equal (a,b)
        else if Term.is_const a andalso Term.is_const b then
          let
            val x = Term.dest_thy_const a
            val y = Term.dest_thy_const b
            val _ = observe (1 + IntInf.fromInt
              (String.size (#Thy x) + String.size (#Name x) +
               String.size (#Thy y) + String.size (#Name y)))
            val _ = type_work observe (#Ty x)
            val _ = type_work observe (#Ty y)
          in #Thy x = #Thy y andalso #Name x = #Name y andalso
             Type.compare (#Ty x,#Ty y) = EQUAL end
        else (observe 1; false)
      fun walk environment (left,right) =
        let
          val _ = observe 1
          val lf = free left
          val rf = free right
          val environment = List.filter (fn (a,b,_) =>
            (observe 1; member equal a lf orelse member equal b rf))
            environment
          val key = (identity left,identity right,
            List.map (fn (_,_,id) => (observe 1; id)) environment)
        in case Redblackmap.peek (!memo,key) of SOME result => result
         | NONE =>
           let
             val result = case (read left,read right) of
                 (Variable a,Variable b) => variables environment (a,b)
               | (Atom a,Atom b) => atom (a,b)
               | (Apply (f,x),Apply (g,y)) =>
                   walk environment (f,g) andalso walk environment (x,y)
               | (Abstract (a,x),Abstract (b,y)) =>
                   let
                     val aty = Term.type_of a
                     val bty = Term.type_of b
                     val _ = type_work observe aty
                     val _ = type_work observe bty
                     val _ = serial := !serial + 1
                   in Type.compare (aty,bty) = EQUAL andalso
                      walk ((a,b,!serial)::environment) (x,y) end
               | _ => false
             val _ = observe 1
             val _ = memo := Redblackmap.insert (!memo,key,result)
           in result end
        end
    in walk [] (left,right) end

  (* Substitute into source syntax, not into a realized graph. Memoize by
     syntax AND its relevant lexical bindings. Fresh bindings at unrelated
     abstractions must not split the cache for a shared child. Only admitted
     native fragments are opened; actual operands remain shared syntax. *)
  fun substitute observe replacements root =
    let
      val resolve = private_reader observe
      val entries = observations observe
      val equal = same_variable observe
      fun free syntax = free_occurrences observe (entries syntax)
      val serial = ref (0 : IntInf.int)
      fun compare_variable (left,right) =
        let val (a,aty) = Term.dest_var left
            val (b,bty) = Term.dest_var right
            val _ = observe (1+IntInf.fromInt (String.size a+String.size b))
            val _ = type_work observe aty
            val _ = type_work observe bty
        in Term.compare (left,right) end
      val interned = ref (Redblackmap.mkDict compare_variable)
      fun same_source (Syntax {id=a,node=left,...},
                       Syntax {id=b,node=right,...}) =
        (observe 1; a=b orelse
         (case (left,right) of
            (Native x,Native y) => Term.is_var x andalso Term.is_var y
              andalso equal (x,y)
          | (Private x,Private y) => equal (x,y)
          | _ => false))
      (* A Renaming may reach the same shared child through distinct source
         wrappers. Intern equivalent bindings, not wrapper/visit identities.
         Native comparisons here are ONLY between atomic variables. *)
      fun binding (old,value,variables,active,lexical) =
        let
          val _ = observe 1
          val bucket = case Redblackmap.peek (!interned,old) of
              NONE => [] | SOME bucket => bucket
          fun matches (_,source,vars,act,lex,_) =
            (observe 1; active=act andalso lexical=lex andalso
             same_source (value,source) andalso
             List.collate compare_variable (variables,vars)=EQUAL)
        in case List.find matches bucket of
            SOME entry => entry
          | NONE =>
            let val _ = serial := !serial+1
                val entry = (old,value,variables,active,lexical,!serial)
                val _ = observe 1
                val _ = interned :=
                  Redblackmap.insert (!interned,old,entry::bucket)
            in entry end
        end
      fun compare_id (left,right) =
        (observe 1; IntInf.compare (left,right))
      val memo = ref (Redblackmap.mkDict
        (fn ((a,b),(c,d)) => (observe 1;
          case List.collate compare_id (a,c) of
            EQUAL => compare_id (b,d) | x => x)))
      fun lookup variable [] = (observe 1; NONE)
        | lookup variable ((old,value,variables,active,lexical,_)::rest) =
            if equal (variable,old) then SOME (value,variables,active,lexical)
            else lookup variable rest
      fun extend bindings rest = bindings @ List.filter
        (fn (old,_,_,_,_,_) => not (Option.isSome (lookup old bindings))) rest
      fun source_variable (Syntax {node,...}) =
        (observe 1; case node of
           Native term => if Term.is_var term then SOME term else NONE
         | Private _ => NONE
         | Template source => source_variable (expand_template observe source)
         | Renaming (body,renamed) => Option.map
             (replace observe renamed) (source_variable body)
         | _ => NONE)
      fun fresh avoids variable =
        let
          val bytes = List.foldl (fn (avoid,total) =>
            (observe 1; total+1+IntInf.fromInt
              (String.size (#1 (Term.dest_var avoid))))) 0 avoids
          val result = Term.prim_variant avoids variable
          val size = IntInf.fromInt (String.size (#1 (Term.dest_var result)))
          val original = IntInf.fromInt
            (String.size (#1 (Term.dest_var variable)))
          val _ = observe ((size-original+1)*(bytes+size+1))
        in result end
      fun walk [] syntax = syntax
        | walk bindings (syntax as Syntax {id,ty,node,...}) =
        let
          val _ = observe 1
          val current = free syntax
          (* Keep inactive lexical bindings too: capture avoidance needs
             their public names, not just active replacement ranges. Order
             and identities survive projection, preserving first lookup. *)
          val bindings = List.filter (fn (old,_,_,_,_,_) =>
            (observe 1; member equal old current)) bindings
          (* Independent simultaneous renamings can commute. Their binding
             order is irrelevant to lookup, but not to a raw list cache key.
             Sort ONLY the key; stable sorting retains duplicate-domain
             precedence, and the visitor keeps its original binding order. *)
          val ordered = Listsort.sort
            (fn ((left,_,_,_,_,_),(right,_,_,_,_,_)) =>
              compare_variable (left,right)) bindings
          val key = (List.map (fn (_,_,_,_,_,identity) =>
            (observe 1; identity)) ordered,id)
        in
         if null bindings then syntax
         else case Redblackmap.peek (!memo,key) of SOME result => result
         | NONE =>
           let
             val result = case node of
                 Native term => if Term.is_var term then
                   (case lookup term bindings of SOME (value,_,_,_) => value
                    | NONE => syntax)
                 else if Term.is_abs term orelse Term.is_comb term then
                   walk bindings (expand_template_mode true observe
                     {template=term,holes=[],operands=[],avoids=NONE})
                 else syntax
               | Private _ => syntax
               | PrivateBinding _ => walk bindings (resolve syntax)
               | Template source =>
                   walk bindings (expand_template observe source)
               | Application (operator,operand) =>
                   application (walk bindings operator,walk bindings operand)
               | Renaming (body,renamed) =>
                   let val changed = List.map (fn (old,value) =>
                         (observe 1; case lookup value bindings of
                           SOME (source,variables,active,lexical) =>
                             binding (old,source,variables,active,lexical)
                         | NONE => binding
                             (old,native value,[value],false,true))) renamed
                   in walk (extend changed bindings) body end
               | Abstraction (stored,marker,body) =>
                   let
                     val bindings = List.filter
                       (fn (old,_,_,_,_,_) => not (equal (old,marker))) bindings
                     val introduced = List.foldl
                       (fn ((old,_,variables,active,_,_),rest) =>
                         (observe 1;
                          if active andalso member equal old current then
                            (observe (IntInf.fromInt (List.length variables));
                             variables @ rest)
                          else rest)) [] bindings
                     val name = #1 (Term.dest_var stored)
                     fun clashes variable =
                       let val other = #1 (Term.dest_var variable)
                           val _ = observe (1+IntInf.fromInt
                             (String.size name+String.size other))
                       in name=other end
                     (* Internal lexical markers are not native free
                        names. Enclosing lexical bindings supply the public
                        binder names which native freshening must avoid. *)
                     val original_free = List.concat (List.map (fn variable =>
                       if equal (variable,marker) then [stored]
                       else case lookup variable bindings of
                         SOME (_,variables,_,true) => variables
                       | _ => [variable]) (free body))
                     val changed = not opening_freshens_names andalso
                       List.exists clashes introduced
                     val binder = if changed then
                         fresh (introduced @ original_free) stored else stored
                     val avoids = all_variables observe (body :: List.map
                       (fn (_,value,_,_,_,_) => value) bindings)
                     val new_marker = fresh (marker::binder::avoids) marker
                     val bindings =
                       binding (marker,native new_marker,[binder],changed,true)
                       :: bindings
                   in make ty
                     (Abstraction (binder,new_marker,walk bindings body)) end
             val _ = observe 1
             val _ = memo := Redblackmap.insert (!memo,key,result)
           in result end
        end
      (* Remove only lexical identities. An equal-spelled private atom is
         still a replacement, not the original lexical variable. *)
      val bindings = List.mapPartial (fn (old,value) =>
        (observe 1; case source_variable value of
           SOME variable => if equal (old,variable) then NONE
             else SOME (binding (old,value,free value,true,false))
         | NONE => SOME (binding (old,value,free value,true,false))))
        replacements
    in if null bindings then root else walk bindings (resolve root) end

  fun normalize_lets observe root =
    let
      val resolve = private_reader observe
      val memo = ref (dictionary observe)
      fun walk (source as Syntax {id,ty,node,...}) =
        (observe 1;case Redblackmap.peek (!memo,id) of
           SOME result => result
         | NONE =>
           let val result = case node of
                 Native _ => source
               | Private _ => source
               | PrivateBinding _ => walk (resolve source)
               | Template template => walk (expand_template observe template)
               | Renaming (body,replacements) => walk (substitute observe
                   (List.map (fn (old,value) => (old,native value))
                     replacements) body)
               | Abstraction (stored,marker,body) =>
                   make ty (Abstraction (stored,marker,walk body))
               | Application (f,x) =>
                   let val f = walk f val x = walk x
                   in case f of
                       Syntax {node=Application (head,function),...} =>
                         if is_constant observe boolSyntax.let_tm head then
                           (case dest_abs observe function of
                              SOME (variable,body) =>
                                (case view observe body of
                                   Variable term =>
                                     if Term.compare (term,variable)=EQUAL
                                     then x
                                     else walk (substitute observe
                                       [(variable,x)] body)
                                 | _ => walk (substitute observe
                                     [(variable,x)] body))
                            | NONE => application (f,x))
                         else application (f,x)
                     | _ => application (f,x)
                   end
               val _ = observe 1
               val _ = memo := Redblackmap.insert (!memo,id,result)
           in result end)
    in walk (resolve root) end
end
