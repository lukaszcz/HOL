structure benchMeasures =
struct

open HolKernel

fun named name theorem : benchLib.named_thm =
  {name = name, theorem = theorem}

fun entry id line method recipe goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method,
   recipe = recipe, excl = [], provenance =
     {file = "src/HOL/List.thy", line = line, commit = "f7e02b7e"},
   representative = false}

val definition =
  benchLib.DefinitionAdd
    (named "parityTranslation$source_measures_def"
       parityTranslationTheory.source_measures_def)

val simp = benchLib.Invoke (benchLib.Simp, [definition])

val goals =
  [entry "list_L7771_wf_measures" 7771
     "unfolding measures_def by blast"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.RewriteAdd
           (named "parityTranslation$source_measures_WF"
              parityTranslationTheory.source_measures_WF)]))
     ``!functions.
         relation$WF
           (parityTranslation$source_measures functions)``,
   entry "list_L7775_in_measures_1" 7775
     "unfolding measures_def by auto" simp
     ``!left right.
         ~parityTranslation$source_measures [] left right``,
   entry "list_L7775_in_measures_2" 7775
     "unfolding measures_def by auto" simp
     ``!function functions left right.
         (parityTranslation$source_measures
            (function::functions) left right <=>
          function left < function right \/
          (function left = function right /\
           parityTranslation$source_measures
             functions left right))``,
   entry "list_L7782_measures_less" 7782 "by simp" simp
     ``!function functions left right.
         function left < function right ==>
         parityTranslation$source_measures
           (function::functions) left right``,
   entry "list_L7785_measures_lesseq" 7785 "by auto"
     (benchLib.Invoke (benchLib.Auto, [definition]))
     ``!function functions left right.
         function left <= function right ==>
         parityTranslation$source_measures functions left right ==>
         parityTranslation$source_measures
           (function::functions) left right``]

val shortfalls : benchLib.shortfall list = []

end
