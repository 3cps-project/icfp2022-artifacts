(* hash-set-fn.sml
 * 
 * Taken and modified from the SMLNJ 110.97 basis library 
 *)

signature MY_MONO_HASH_SET =
  sig

    structure Key : HASH_KEY

    type item = Key.hash_key
    type set

    val mkEmpty : int -> set
	(* The empty set; argument specifies initial table size *)

    val mkSingleton : item -> set
	(* Create a singleton set *)

    val mkFromList : item list -> set
	(* create a set from a list of items *)

    val add  : set * item -> bool
    val addc : set -> item -> bool
	(* Insert an item. *)

    val addList : set * item list -> unit
	(* Insert items from list. *)

    val without : set * item -> unit
	(* Remove the item, if it is in the set.  Otherwise the set is unchanged. *)

    val delete : set * item -> bool
	(* Remove an item.  Return false if the item was not present. *)

    val member : set * item -> bool
	(* Return true if and only if item is an element in the set *)

    val isEmpty : set -> bool
	(* Return true if and only if the set is empty *)

    val isSubset : (set * set) -> bool
	(* Return true if and only if the first set is a subset of the second *)

    val numItems : set ->  int
	(* Return the number of items in the table *)

    val listItems : set -> item list
	(* Return a list of the items in the set *)

    val map : (item -> item) -> set -> set
	(* Create a new set by applying a map function to the elements
	 * of the set.
         *)

    val app : (item -> unit) -> set -> unit
	(* Apply a function to the entries of the set. *)

    val fold : (item * 'b -> 'b) -> 'b -> set -> 'b
	(* Apply a folding function to the entries of the set. *)

    val filter : (item -> bool) -> set -> unit

    val copy : set -> set

  end (* MY_MONO_HASH_SET *)

functor MyHashSetFn (Key : HASH_KEY) =
  struct

    structure Key = Key
  (* NOTE: someday we will change the HASH_KEY signature to follow the naming conventions of
   * the SML basis, so we use those names internally to ease future porting.
   *)
    type item = Key.hash_key
    val hash = Key.hashVal
    val same = Key.sameKey

    datatype bucket
      = NIL
      | B of (word * item * bucket)

    datatype set = SET of {
	table : bucket array ref,
	nItems : int ref
      }

    fun index (i, sz) = Word.toIntX(Word.andb(i, Word.fromInt sz - 0w1))

  (* minimum and maximum hash table sizes.  We use powers of two for hash table
   * sizes, since that give efficient indexing, and assume a minimum size of 32.
   *)
    val minSize = 2
    (* TODO: the following crashes MLton with an Overflow... nice *)
    (*
    val maxSize = let
	fun f i = let
	    val i' = i+i
	in
	    if i' < Array.maxLen then f i' else i
	end
    in
	f 0x10000
    end
    *)
    (* So for now, max size = 1000000 \aprrox 2^20 *)
    val maxSize = 1000000

  (* round up `n` to the next hash-table size *)
    fun roundUp n =
        if (n >= maxSize)
	then maxSize
        else if (n < minSize)
        then minSize
        else n

  (* Create a new table; the int is a size hint and the exception
   * is to be raised by find.
   *)
    fun alloc sizeHint = Array.array(roundUp sizeHint, NIL)

  (* grow a table to the specified size *)
    fun growTable (table, newSz) = let
	  val newArr = Array.array (newSz, NIL)
	  fun copy NIL = ()
	    | copy (B(h, key, rest)) = let
		val indx = index (h, newSz)
		in
		  Array.update (newArr, indx, B(h, key, Array.sub(newArr, indx)));
		  copy rest
		end
	  in
	    Array.app copy table;
	    newArr
	  end

  (* conditionally grow a table; return true if it grew. *)
    fun growTableIfNeeded (table, nItems) = let
	    val arr = !table
	    val sz = Array.length arr
	    in
	      if (nItems >= sz)
		then (table := growTable (arr, sz+sz); true)
		else false
	    end

  (* reverse-append for buckets *)
    fun revAppend (NIL, b) = b
      | revAppend (B(h, x, r), b) = revAppend(r, B(h, x, b))

  (* Add an item to a set *)
    fun add (tbl as SET{table, nItems}, item) = let
	  val arr = !table
	  val sz = Array.length arr
	  val h = hash item
	  val indx = index (h, sz)
          val res = ref true
	  fun look NIL = (
		Array.update(arr, indx, B(h, item, Array.sub(arr, indx)));
		nItems := !nItems + 1;
		growTableIfNeeded (table, !nItems);
		NIL)
	    | look (B(h', item', r)) = if ((h = h') andalso same(item, item'))
		then (res := false; NIL) (* item already present *)
		else (case (look r)
		   of NIL => NIL
		    | rest => B(h', item', rest)
		  (* end case *))
	  in
	    (case (look (Array.sub (arr, indx)))
	      of NIL => ()
	       | b => Array.update(arr, indx, b)
	     (* end case *);
             ! res)
	  end
    fun addc set item = add(set, item)

  (* The empty set *)
    fun mkEmpty sizeHint = SET{
	    table = ref (alloc sizeHint),
	    nItems = ref 0
	  }

  (* Create a singleton set *)
    fun mkSingleton item = let
          val set = mkEmpty minSize
          in
            add (set, item);
            set
          end

  (* create a set from a list of items *)
    fun mkFromList items = let
          val set = mkEmpty(List.length items)
          in
            List.app (fn i => (add (set, i); ())) items;
            set
          end

  (* Insert items from list. *)
    fun addList (set, items) = List.app (fn i => (add (set, i); ())) items

  (* Remove an item. Raise NotFound if not found. *)
    fun delete (SET{table, nItems}, item) = let
	  val arr = !table
	  val sz = Array.length arr
	  val h = hash item
	  val indx = index (h, sz)
	  fun look (_, NIL) = false
	    | look (prefix, B(h', item', r)) = if ((h = h') andalso same(item, item'))
		then (
                  Array.update(arr, indx, revAppend(prefix, r));
                  nItems := !nItems - 1;
                  true)
		else look (B(h', item', prefix), r)
          in
            look (NIL, Array.sub(arr, indx))
          end

  (* Remove the item, if it is in the set.  Otherwise the set is unchanged. *)
    fun without (set, item) = ignore(delete (set, item))

  (* Return true if and only if item is an element in the set *)
    fun member (SET{table, ...}, item) = let
	  val arr = !table
	  val sz = Array.length arr
	  val h = hash item
	  val indx = index (h, sz)
	  fun look NIL = false
	    | look (B(h', item', r)) = ((h = h') andalso same(item, item')) orelse look r
          in
            look (Array.sub(arr, indx))
          end

  (* Return true if and only if the set is empty *)
    fun isEmpty (SET{nItems, ...}) = (!nItems = 0)

  (* Return true if and only if the first set is a subset of the second *)
    fun isSubset (SET{table=tbl1, nItems=n1}, s2 as SET{table=tbl2, nItems=n2}) =
          if (!n1 <= !n2)
            then let
              val arr1 = !tbl1 and arr2 = !tbl2
              val sz1 = Array.length arr1 and sz2 = Array.length arr2
              fun lp i = if (i <= sz1)
                    then let
                    (* iterate over the items in bucket i *)
                      fun look1 NIL = lp(i+1)
                        | look1 (B(h, item, r)) = let
                          (* search s2 for the item *)
                            fun look2 NIL = false
                              | look2 (B(h', item', r')) =
                                  if ((h = h') andalso same(item, item'))
                                    then look1 r
                                    else look2 r'
                            in
                              look2 (Array.sub(arr2, index (h, sz2)))
                            end
                      in
                        look1 (Array.sub(arr1, i))
                      end
                    else true
              in
                lp 0
              end
            else false

  (* Return the number of items in the table *)
    fun numItems (SET{nItems, ...}) = !nItems

  (* Return a list of the items in the set *)
    fun listItems (SET{table, nItems}) =
          if (!nItems = 0)
            then []
            else let
              fun f (NIL, l) = l
                | f (B(_, x, r), l) = f(r, x::l)
              in
                Array.foldl f [] (!table)
              end

  (* Create a new set by applying a map function to the elements
   * of the set.
   *)
    fun map f (SET{nItems, table}) = let
          val s = mkEmpty (!nItems)
          fun mapf NIL = ()
            | mapf (B(_, x, r)) = (add(s, f x); mapf r)
          in
            Array.app mapf (!table);
            s
          end

  (* Apply a function to the entries of the set. *)
    fun app f (SET{nItems, table}) = let
          fun appf NIL = ()
            | appf (B(_, x, r)) = (f x; appf r)
          in
            Array.app appf (!table)
          end

  (* Apply a folding function to the entries of the set. *)
    fun fold f init (SET{nItems, table}) = let
          fun foldf (NIL, acc) = acc
            | foldf (B(_, x, r), acc) = foldf (r, f(x, acc))
          in
            Array.foldl foldf init (!table)
          end

    fun copy (SET{nItems, table}) = let
        val arr = ! table
        val arr' = alloc (Array.length arr)
        val table' = ref arr'
        val _ = ref (Array.copy {src = arr, dst = arr', di = 0})
        val nItems' = ref (! nItems)
    in SET{nItems=nItems', table=table'} end

  (* Remove elements that do not satisfy the filter *)
    fun filter f (SET{nItems, table}) = let
          fun loc_filter (NIL, acc, cnt) = (if cnt = 0 then () else nItems := (!nItems - cnt); acc)
            | loc_filter (B(h, x, r), acc, cnt) = 
              if f x
              then loc_filter (r, B(h, x, acc), cnt)
              else loc_filter (r, acc, cnt+1)
          fun filterf lst = loc_filter (lst, NIL, 0)
          in
            Array.modify filterf (!table)
          end

  end

