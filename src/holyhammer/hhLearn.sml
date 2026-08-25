structure hhLearn :> hhLearn =
struct

open HolKernel aiLib

val ERR = mk_HOL_ERR "hhLearn"

type constants =
  {init_val : real,
   pos_weight : real,
   def_val : real,
   tau : real,
   def_prior_weight : int,
   max_dependencies : int}

(* Isabelle's sparse-NB constants are kept in one value.  Later tuning must
   replace this record as a whole rather than mixing parameter sets. *)
val default_constants : constants =
  {init_val = 30.0,
   pos_weight = 5.0,
   def_val = ~18.0,
   tau = 0.2,
   def_prior_weight = 1000,
   max_dependencies = 20}

type frequency_table = (int, int) Redblackmap.dict
type weight_table = (int, real) Redblackmap.dict
type idf_table =
  {nfacts : int, dffreq : frequency_table, weights : weight_table}

fun increment key table =
  case Redblackmap.peek (table, key) of
      SOME count => dadd key (count + 1) table
    | NONE => dadd key 1 table

fun create_idf_table facts =
  let
    fun add_fact ((_, features), (nfacts, frequencies)) =
      (nfacts + 1,
       foldl (fn (feature, table) => increment feature table)
         frequencies (mk_fast_set Int.compare features))
    val (nfacts, dffreq) =
      foldl add_fact (0, dempty Int.compare) facts
    val ln_nfacts =
      if nfacts = 0 then 0.0 else Math.ln (Real.fromInt nfacts)
    val weights = dmap (fn (_, frequency) =>
      ln_nfacts - Math.ln (Real.fromInt frequency)) dffreq
  in
    {nfacts = nfacts, dffreq = dffreq, weights = weights}
  end

fun idf_nfacts ({nfacts, ...} : idf_table) = nfacts

fun document_frequency ({dffreq, ...} : idf_table) feature =
  Redblackmap.peek (dffreq, feature)

fun idf_of ({weights, ...} : idf_table) feature =
  Redblackmap.peek (weights, feature)

fun idf_entries ({weights, ...} : idf_table) = dlist weights

type dep_table =
  (mlThmData.thmid, mlThmData.thmid list) Redblackmap.dict

fun dep_table_of entries = dnew String.compare entries

fun build_dep_table dependencies facts =
  foldl
    (fn ((thmid, _), table) =>
      if dmem thmid table then table
      else dadd thmid (dependencies thmid) table)
    (dempty String.compare) facts

fun create_dep_table (_, facts) =
  build_dep_table mlThmData.validdep_of_thmid facts

fun dependencies_of table thmid = Redblackmap.peek (table, thmid)

val dependency_entries = dlist

fun pure_logic_concl conclusion =
  let
    fun pure_constant constant =
      let val {Thy, ...} = dest_thy_const constant in
        Thy = "min" orelse Thy = "bool"
      end
  in
    List.all pure_constant
      (mk_term_set (find_terms is_const conclusion))
  end

type fact_info =
  {thmid : mlThmData.thmid,
   features : mlFeature.fea,
   def : bool,
   concl : term option}

type score_parts =
  {prior : real,
   positive : real,
   absent : real,
   negative : real,
   total : real}

type sparse_frequency = (int, int) Redblackmap.dict
type nb_model =
  {constants : constants,
   idf : idf_table,
   names : mlThmData.thmid vector,
   indices : (mlThmData.thmid, int) Redblackmap.dict,
   tfreq : int vector,
   sfreq : sparse_frequency vector}

fun add_index ((fact : fact_info), (index, table)) =
  let val thmid = #thmid fact in
    if dmem thmid table then
      raise ERR "train_nb" ("duplicate theorem identifier " ^ thmid)
    else (index + 1, dadd thmid index table)
  end

fun add_weight amount key table =
  case Redblackmap.peek (table, key) of
      SOME count => dadd key (count + amount) table
    | NONE => dadd key amount table

fun train_nb constants idf dependencies facts =
  let
    val number = length facts
    val _ =
      if idf_nfacts idf = number then ()
      else raise ERR "train_nb" "IDF and fact-table sizes differ"
    fun require_feature feature =
      if Option.isSome (idf_of idf feature) then ()
      else raise ERR "train_nb" "fact feature is absent from IDF table"
    val _ = List.app
      (fn (fact : fact_info) => List.app require_feature (#features fact))
      facts
    val information = Vector.fromList facts
    val names = Vector.map #thmid information
    val pure_logic = Vector.map
      (fn (fact : fact_info) =>
        case #concl fact of
            SOME conclusion => pure_logic_concl conclusion
          | NONE => false)
      information
    val (_, indices) =
      foldl add_index (0, dempty String.compare) facts
    val tfreq = Array.array (number, 0)
    val sfreq = Array.tabulate (number, fn _ => dempty Int.compare)

    fun add_use weight target features =
      let
        val frequencies = Array.sub (sfreq, target)
        val frequencies' = foldl
          (fn (feature, table) => add_weight weight feature table)
          frequencies features
      in
        Array.update (tfreq, target,
          Array.sub (tfreq, target) + weight);
        Array.update (sfreq, target, frequencies')
      end

    fun pure_dependency thmid =
      let
        val index = dfind thmid indices
      in
        Vector.sub (pure_logic, index)
      end

    fun usable_dependencies (fact : fact_info) =
      case dependencies_of dependencies (#thmid fact) of
          NONE => []
        | SOME raw_dependencies =>
            if #def fact orelse
               length raw_dependencies > #max_dependencies constants orelse
               not (List.all (fn thmid => dmem thmid indices)
                 raw_dependencies)
            then []
            else filter (not o pure_dependency)
              (mk_fast_set String.compare raw_dependencies)

    fun learn index =
      if index = number then ()
      else
        let
          val fact = Vector.sub (information, index)
          val features = mk_fast_set Int.compare (#features fact)
          val _ = add_use (#def_prior_weight constants) index features
          val _ = List.app
            (fn dependency =>
              add_use 1 (dfind dependency indices) features)
            (usable_dependencies fact)
        in
          learn (index + 1)
        end
    val _ = learn 0
  in
    {constants = constants, idf = idf, names = names,
     indices = indices, tfreq = Array.vector tfreq,
     sfreq = Array.vector sfreq}
  end

fun conclusion_of thmid =
  case mlThmData.thm_of_name thmid of
      SOME (_, theorem) => SOME (Thm.concl theorem)
    | NONE => NONE

fun train_nb_from_thmdata constants idf dependencies statures (_, facts) =
  let
    fun fact_info (thmid, features) : fact_info =
      {thmid = thmid, features = features,
       def = #def (hhStature.stature_of statures thmid),
       concl = conclusion_of thmid}
  in
    train_nb constants idf dependencies (map fact_info facts)
  end

fun nb_thmids ({names, ...} : nb_model) = Vector.foldr op:: [] names

fun model_index ({indices, ...} : nb_model) thmid =
  Redblackmap.peek (indices, thmid)

fun nb_tfreq (model as {tfreq, ...} : nb_model) thmid =
  case model_index model thmid of
      SOME index => SOME (Vector.sub (tfreq, index))
    | NONE => NONE

fun nb_sfreq (model as {sfreq, ...} : nb_model) thmid feature =
  case model_index model thmid of
      SOME index => Redblackmap.peek (Vector.sub (sfreq, index), feature)
    | NONE => NONE

fun nb_knows_feature ({idf, ...} : nb_model) feature =
  Option.isSome (idf_of idf feature)

fun known_goal_features ({idf, ...} : nb_model) goal_features =
  let
    fun add ((feature, weight), table) =
      if Option.isSome (idf_of idf feature) then
        case Redblackmap.peek (table, feature) of
            SOME old => dadd feature (old + weight) table
          | NONE => dadd feature weight table
      else table
  in
    dlist (foldl add (dempty Int.compare) goal_features)
  end

fun model_idf ({idf, ...} : nb_model) feature =
  case idf_of idf feature of
      SOME weight => weight
    | NONE => raise ERR "nb_score_parts" "model feature has no IDF weight"

fun nb_score_parts_prepared (model as
      {constants, tfreq, sfreq, ...} : nb_model)
      prepared_goal_features thmid =
  case model_index model thmid of
      NONE => NONE
    | SOME index =>
        let
          val total_frequency = Real.fromInt (Vector.sub (tfreq, index))
          val fact_features = Vector.sub (sfreq, index)
          fun add_goal ((feature, weight),
                (positive, absent, remaining)) =
            let val feature_idf = model_idf model feature in
              case Redblackmap.peek (remaining, feature) of
                  SOME frequency =>
                    (positive + weight * feature_idf *
                       Math.ln (#pos_weight constants *
                         Real.fromInt frequency / total_frequency),
                     absent, drem feature remaining)
                | NONE =>
                    (positive,
                     absent + weight * feature_idf *
                       #def_val constants,
                     remaining)
            end
          val prior = #init_val constants * Math.ln total_frequency
          val (positive, absent, remaining) = foldl add_goal
            (0.0, 0.0, fact_features)
            prepared_goal_features
          fun add_negative (feature, frequency, sum) =
            let
              val feature_idf = model_idf model feature
            in
              sum + feature_idf * Math.ln
                (1.0 - Real.fromInt (frequency - 1) / total_frequency)
            end
          val negative = #tau constants *
            dfoldl add_negative 0.0 remaining
          val total = prior + positive + absent + negative
        in
          SOME {prior = prior, positive = positive, absent = absent,
                negative = negative, total = total}
        end

fun nb_score_parts model goal_features thmid =
  nb_score_parts_prepared model
    (known_goal_features model goal_features) thmid

fun nb_scores model {pool, goal_features} =
  let
    (* Normalization is query-wide.  Keeping it outside the candidate loop is
       load-bearing for the large pools used by the live hammer. *)
    val prepared_goal_features = known_goal_features model goal_features
  in
    List.mapPartial
      (fn thmid =>
        case nb_score_parts_prepared model prepared_goal_features thmid of
            SOME parts => SOME (thmid, #total parts)
          | NONE => NONE)
      pool
  end

fun take count items =
  let
    fun loop 0 _ result = rev result
      | loop _ [] result = rev result
      | loop left (item :: rest) result =
          loop (left - 1) rest (item :: result)
  in
    if count <= 0 then [] else loop count items []
  end

fun nb_rank model {pool, goal_features, n} =
  nb_scores model {pool = pool, goal_features = goal_features}
  |> Listsort.sort
       (fn ((_, left), (_, right)) => Real.compare (right, left))
  |> take n
  |> map #1

end
