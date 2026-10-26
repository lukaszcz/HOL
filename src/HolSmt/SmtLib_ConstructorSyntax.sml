(* Ordinary-source observations only. No graph constants, materialisation,
   equality decisions, or proof authority live here.

   Operands are shared, never copied into a native template. Constructors do
   only local work (from_template validates its hole/operand lists). Callers
   admit the retained native templates and account for construction work;
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

  datatype syntax = Syntax of
    {id : IntInf.int, ty : Type.hol_type, node : node}
  and node =
      Native of Term.term
    | Template of {template : Term.term, holes : Term.term list,
                   operands : syntax list, avoids : Term.term list option}
    | Application of syntax * syntax
    | Abstraction of Term.term * Term.term * syntax
    (* Simultaneous FREE-variable renaming. Unlike rebuilding named lambdas,
       this preserves stored inner binder names even on a name collision.
       It describes the de Bruijn opening performed by ordinary dest_abs. *)
    | Renaming of syntax * (Term.term * Term.term) list

  fun make ty node =
    let val id = !serial
    in serial := id + 1; Syntax {id = id, ty = ty, node = node} end
  fun type_of (Syntax {ty, ...}) = ty
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
  fun expand_template (observe : IntInf.int -> unit)
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
            | NONE => native term)
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

  (* Entries retain the distinction between stored binders and free
     occurrences. Removing a free variable from an untagged all-vars set
     would incorrectly remove an equal variable stored by an inner binder.
     First-occurrence order is retained so all_variables also reproduces
     the ordinary all_varsl list order, not just its set of variables. *)
  datatype occurrence = Free of Term.term | Bound of Term.term
  fun variable_of (Free variable) = variable
    | variable_of (Bound variable) = variable
  fun same_occurrence observe (Free left, Free right) =
        same_variable observe (left, right)
    | same_occurrence observe (Bound left, Bound right) =
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

  fun free_variables (observe : IntInf.int -> unit) entries =
    List.foldr (fn (Free variable, rest) =>
                       (observe 1; variable :: rest)
                 | (Bound _, rest) => (observe 1; rest)) [] entries

  fun replace observe replacements variable =
    let
      fun find [] = (observe 1; variable)
        | find ((old, replacement) :: rest) =
            if same_variable observe (old, variable) then replacement
            else find rest
    in find replacements end

  (* Open only retained native source syntax with the public dest_abs.
     Its exposed binder may be freshened: remove its FREE occurrences, but
     retain all stored inner binders and record the original stored binder.
     This preserves exact all_varsl names and order, not just alpha-equivalence.
     No native term is assembled from synthetic operands by this visitor. *)
  fun observations observe =
    let
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
                 | Bound _ => (observe 1; true)) (native_variables body)
           in merge ([Bound stored], entries) end
         else [])
      fun visit (Syntax {id, node, ...}) =
        (observe 1;
         case Redblackmap.peek (!memo, id) of
           SOME entries => entries
         | NONE =>
           let
             val entries =
               case node of
                 Native term => native_variables term
               | Template source => visit (expand_template observe source)
               | Application (operator, operand) =>
                   merge (visit operator, visit operand)
               | Abstraction (stored, binder, body) =>
                   let
                     val entries = List.filter
                       (fn Free variable =>
                             not (same_variable observe (binder, variable))
                         | Bound _ => (observe 1; true)) (visit body)
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
    in visit end

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
               | Template source => visit (expand_template observe source)
               | Application (operator, operand) =>
                   visit operator orelse visit operand
               | Abstraction (_, _, body) => visit body
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

  (* Ordinary substitution does not capture free source operands. Keep
     stored binder names separate from fresh bound-occurrence markers. *)
  fun from_substitution observe (source as {template,holes,operands}) =
    from_template_mode (SOME (holes @ all_variables observe operands)) source

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

  fun strip_abs observe root =
    let
      val entries = observations observe
      val heads = ref (dictionary observe)
      fun free body = free_variables observe (entries body)
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
               | Template source => head (expand_template observe source)
               | Abstraction (stored, marker, body) =>
                   SOME (stored, marker, body)
               | Native term =>
                   if not (Term.is_abs term) then NONE
                   else
                     let
                       val stored = stored_binder observe term
                       val marker = fresh (stored :: free syntax) stored
                       val _ = native_work term
                       (* A private fresh marker avoids dest_abs's native
                          clash/retry/free_vars path. The stored name is
                          restored by peel, using the source free names. *)
                       val opened_term = Term.rename_bvar
                         (#1 (Term.dest_var marker)) term
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
      fun peel syntax prefix =
        (observe 1;
         case head syntax of
           NONE => (List.rev prefix, syntax)
         | SOME (stored, marker, body) =>
           let
             val avoids = without marker (free body)
             val name = #1 (Term.dest_var stored)
             fun clashes variable =
               let val other = #1 (Term.dest_var variable)
                   val _ = observe (1 + IntInf.fromInt
                     (String.size name + String.size other))
               in name = other end
             val binder = if List.exists clashes avoids
                          then fresh avoids stored else stored
             val body = if same_variable observe (marker, binder) then body
                        else renamed (body, [(marker, binder)])
           in peel body (binder :: prefix) end)
    in peel root [] end
end
