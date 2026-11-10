signature SmtLib_CarrierTraversalTransport =
sig
  (* Required trusted implementation, not a caller theorem callback record.
     Every focus retains its exact node, actual frames and admission recipe. *)
  type owner
  type focus
  type conversion
  datatype shape = Atomic | Application of focus * focus | Binder of focus

  val validate_owner : owner -> unit
  val validate_focus : owner -> focus -> unit
  val retire : owner -> unit
  (* Debit the SAME invocation work portfolio before each control transition.
     This is not a bound for the internal work of the other operations. *)
  val control : owner -> unit

  val view : owner -> focus -> shape
  val carrier : owner -> focus -> conversion option
  val beta : owner -> focus -> conversion option
  val validate_conversion : owner -> focus -> conversion -> unit
  val target : owner -> conversion -> focus
  val compose : owner -> conversion -> conversion -> conversion
  val lift_application : owner -> focus ->
    conversion option * conversion option -> conversion
  val lift_binder : owner -> focus -> conversion -> conversion
  (* Checked, bounded alpha equivalence, not node-ID inequality. *)
  val alpha_changed : owner -> focus -> conversion -> bool
end

signature SmtLib_CarrierTopDepth =
sig
  type owner
  type focus
  type conversion
  type session
  (* The owner is already established; this creates no Source or budget. *)
  val start : owner -> focus -> session
  val run : session -> conversion option
  val close : session -> unit
end

functor SmtLib_CarrierTopDepthFn
  (T : SmtLib_CarrierTraversalTransport) :>
    SmtLib_CarrierTopDepth
      where type owner = T.owner
      where type focus = T.focus
      where type conversion = T.conversion =
struct
  type owner = T.owner
  type focus = T.focus
  type conversion = T.conversion
  datatype state = Ready | Running | Complete | Retired
  datatype session = Session of
    {owner : owner, original : focus, state : state ref}

  type execution = {owner : owner, state : state ref}

  fun held ({owner, ...} : execution) = owner

  fun active (execution as {state, ...} : execution) =
    (if !state = Running then ()
     else raise Fail "carrier traversal session is not running";
     T.validate_owner (held execution))

  fun guarded owner focus operation =
    (active owner;
     T.validate_focus (held owner) focus;
     let val result = operation ()
     in active owner;
        T.validate_focus (held owner) focus;
        result
     end)

  fun control owner focus =
    guarded owner focus (fn () => T.control (held owner))

  fun checked owner original conversion =
    (guarded owner original
       (fn () => T.validate_conversion (held owner) original conversion);
     let
       val result = guarded owner original
         (fn () => T.target (held owner) conversion)
     in
       T.validate_focus (held owner) result;
       result
     end)

  fun after owner original NONE = original
    | after owner original (SOME conversion) =
        checked owner original conversion

  fun join owner original NONE second =
        (ignore (after owner original second); second)
    | join owner original first NONE =
        (ignore (after owner original first); first)
    | join owner original (SOME first) (SOME second) =
        let
          val middle = checked owner original first
          val _ = checked owner middle second
          val _ = control owner original
          val result = guarded owner original
            (fn () => T.compose (held owner) first second)
          val _ = checked owner original result
        in SOME result end

  fun probe owner root focus =
    let
      val _ = control owner focus
      val result = guarded owner focus (fn () => root (held owner) focus)
      val _ = after owner focus result
    in result end

  fun repeat owner root original =
    let
      fun next current accumulated =
        case probe owner root current of
          NONE => (current, accumulated)
        | SOME conversion =>
            let
              val target = checked owner current conversion
              val joined = join owner original accumulated (SOME conversion)
            in next target joined end
    in next original NONE end

  (* Exact TOP_DEPTH order: repeated root, children, changed-child root retry.
     The retry is ONE root call; success restarts the entire top traversal. *)
  fun top owner root original =
    let
      val _ = control owner original
      val (middle, initial) = repeat owner root original
      val descent = descend owner root middle
    in
      case descent of
        NONE => initial
      | SOME conversion =>
          let
            val target = checked owner middle conversion
            val changed = guarded owner middle
              (fn () => T.alpha_changed (held owner) middle conversion)
          in
            if not changed then initial
            else
              let
                val prefix = join owner original initial (SOME conversion)
              in
                case probe owner root target of
                  NONE => prefix
                | SOME retry =>
                    let
                      val restarted = checked owner target retry
                      val prefix = join owner original prefix (SOME retry)
                      val suffix = top owner root restarted
                    in join owner original prefix suffix end
              end
          end
    end
  and descend owner root original =
    let
      val _ = control owner original
      val shape = guarded owner original
        (fn () => T.view (held owner) original)
    in
      case shape of
        T.Atomic => NONE
      | T.Application (rator, rand) =>
          let
            (* COMB2_CONV evaluates RATOR before the original RAND. *)
            val left = top owner root rator
            val right = top owner root rand
          in
            case (left, right) of
              (NONE, NONE) => NONE
            | _ =>
                let
                  val _ = control owner original
                  val result = guarded owner original
                    (fn () =>
                      T.lift_application (held owner) original (left, right))
                  val _ = checked owner original result
                in SOME result end
          end
      | T.Binder body =>
          (case top owner root body of
             NONE => NONE
           | SOME conversion =>
               let
                 val _ = control owner original
                 val result = guarded owner original
                   (fn () => T.lift_binder (held owner) original conversion)
                 val _ = checked owner original result
               in SOME result end)
    end

  fun start owner original =
    (T.validate_owner owner;
     T.validate_focus owner original;
     Session {owner = owner, original = original, state = ref Ready})

  fun retire (Session {owner, state, ...}) =
    (state := Retired; T.retire owner handle _ => ())

  fun run (session as Session {owner, original, state}) =
    let
      fun require_running () =
        if !state = Running then T.validate_owner owner
        else raise Fail "carrier traversal session retired during operation"
    in
      ((if !state = Ready then ()
        else raise Fail "carrier traversal session is not fresh";
        T.validate_owner owner;
        T.validate_focus owner original;
        state := Running;
        let
          val execution = {owner = owner, state = state}
          val carrier = top execution T.carrier original
          val _ = require_running ()
          val middle = after execution original carrier
          (* No beta operation runs before carrier traversal finishes. *)
          val beta = top execution T.beta middle
          val _ = require_running ()
          val result = join execution original carrier beta
          val _ = require_running ()
          val _ = after execution original result
        in
          state := Complete;
          result
        end)
       handle primary => (retire session; raise primary))
    end

  val close = retire
end

(* Qualified value hint makes the functor visible to Holdep consumers. *)
structure SmtLib_CarrierTopDepthFn = struct val loaded = () end
