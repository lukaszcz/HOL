structure SmtLib_OutputFragments :> SmtLib_OutputFragments =
struct
  datatype doc = Doc of string Redblackset.set * node
  and node =
      Text of string
    | Reference of string
    | Concat of doc list
    | Let of string * doc * doc

  val no_references = Redblackset.empty String.compare

  fun free_references (Doc (references,_)) = references

  fun text fragment = Doc (no_references,Text fragment)

  fun reference name =
    Doc (Redblackset.singleton String.compare name,Reference name)

  fun mentions_reference (document,name) =
    Redblackset.member (free_references document,name)

  fun concat [document] = document
    | concat documents =
        let val references = List.foldl
          (fn (document,known) =>
            Redblackset.union (known,free_references document))
          no_references documents
        in Doc (references,Concat documents) end

  fun join separator [] = concat []
    | join separator (first :: rest) =
        let
          val between = text separator
          fun collect [] reversed = concat (List.rev reversed)
            | collect (document :: remaining) reversed =
                collect remaining (document :: between :: reversed)
        in
          collect rest [first]
        end

  fun let_binding (name,value,body) =
    let
      val body_references = free_references body
      val body_references =
        if Redblackset.member (body_references,name) then
          Redblackset.delete (body_references,name)
        else body_references
      val references =
        Redblackset.union (free_references value,body_references)
    in
      Doc (references,Let (name,value,body))
    end

  datatype frame = Documents of doc list | Bytes of string

  fun render sink document =
    let
      fun visit [] = ()
        | visit (Bytes fragment :: pending) = (sink fragment;visit pending)
        | visit (Documents [] :: pending) = visit pending
        | visit (Documents (Doc (_,current) :: remaining) :: pending) =
            case current of
              Text fragment =>
                (sink fragment;visit (Documents remaining :: pending))
            | Reference name =>
                (sink name;visit (Documents remaining :: pending))
            | Concat children =>
                visit (Documents children :: Documents remaining :: pending)
            | Let (name,value,body) =>
                (sink ("(let ((" ^ name ^ " ");
                 visit (Documents [value] :: Bytes ")) " ::
                   Documents [body] :: Bytes ")" ::
                   Documents remaining :: pending))
    in
      visit [Documents [document]]
    end
end
