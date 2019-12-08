open Ast

exception Type_error
exception Not_found
exception Write_toSelf
exception Unequal_Lengths
exception Class_notExist
exception Self_notFound
exception Id_notFound

type env = (string * typ) list 

fun built_in c =
    (case c
      of "Object"  => true
       | "Integer" => true
       | "String"  => true
       | "Bot"     => true
       | _         => false)

fun defined_class (p:prog) (c:string):bool = 
    let fun class_exists cls c =
        if (#cls_name cls) = c then
            true
        else 
            built_in c

        fun find_class [] c      = built_in c
          | find_class (x::xs) c = 
            if class_exists x c then
                true
            else
                find_class xs c

    in find_class (#prog_clss p) c
    end

fun no_builtin_redef (p:prog):bool = 
    let fun no_redef []      = true
          | no_redef (x::xs) = 
            if built_in (#cls_name x) then
                false
            else
                no_redef xs
    
    in no_redef (#prog_clss p)
    end

fun extract_cls_option opt =
    (case opt
      of NONE     => raise Class_notExist 
       | (SOME x) => x)

fun extract_self_option opt =
    (case opt
      of NONE     => raise Self_notFound
       | (SOME x) => x)

fun extract_id_option opt =
    (case opt
      of NONE     => raise Id_notFound 
       | (SOME x) => x)

fun find_class [] c      = NONE 
  | find_class (x::xs) c = 
    let val { cls_name   = cls_name, 
              cls_super  = _, 
              cls_fields = _, 
              cls_meths  = _ } = x
    in
        if cls_name = c then
            SOME x
        else 
            find_class xs c
    end

fun meth_type (m:meth):mtyp = 
    let val { meth_name   = _,
              meth_ret    = m_ret,
              meth_args   = m_args,
              meth_locals = _,
              meth_body   = _ } = m

        val (_, arg_types) = ListPair.unzip m_args

    in (arg_types, m_ret)
    end

fun built_in_meth (c:string) (m:string):mtyp option =
    (case (c, m)
      of ("Object", "equal?")  => SOME ([TClass "Object"], TClass "Object")
       | ("Object", "to_s")    => SOME ([], TClass "String")
       | ("Object", "print")   => SOME ([], TClass "Bot")
       | ("String", "equal?")  => SOME ([TClass "Object"], TClass "Object")
       | ("String", "to_s")    => SOME ([], TClass "String")
       | ("String", "print")   => SOME ([], TClass "Bot")
       | ("String", "+")       => SOME ([TClass "String"], TClass "String")
       | ("String", "length")  => SOME ([], TClass "Integer")
       | ("Integer", "equal?") => SOME ([TClass "Object"], TClass "Object")
       | ("Integer", "to_s")   => SOME ([], TClass "String")
       | ("Integer", "print")  => SOME ([], TClass "Bot")
       | ("Integer", "+")      => SOME ([TClass "Integer"], TClass "Integer")
       | ("Integer", "-")      => SOME ([TClass "Integer"], TClass "Integer")
       | ("Integer", "*")      => SOME ([TClass "Integer"], TClass "Integer")
       | ("Integer", "/")      => SOME ([TClass "Integer"], TClass "Integer")
       | ("Bot", "equal?")     => SOME ([TClass "Object"], TClass "Object")
       | ("Bot", "to_s")       => SOME ([], TClass "String")
       | ("Bot", "print")      => SOME ([], TClass "Bot")
       | (_, _) => raise Not_found)
    

fun non_built_in (p:prog) (c:string) (m:string):mtyp option =
    let val cls = extract_cls_option (find_class (#prog_clss p) c)
        val meth_list = #cls_meths cls
        
        fun meth [] m      = NONE
          | meth (x::xs) m = 
            if (#meth_name x) = m then
                SOME (meth_type x)
            else
                meth xs m
    
    in meth meth_list m
    end

fun get_meth (p:prog) (c:string) (m:string):mtyp option = 
    (case built_in c
      of true  => built_in_meth c m
       | false => non_built_in p c m)

fun lookup_meth (p:prog) (c:string) (m:string):mtyp =
    (case get_meth p c m
      of SOME x => x 
       | NONE   => 
         let val cls = extract_cls_option (find_class (#prog_clss p) c)
         in lookup_meth p (#cls_super cls) m
         end )

fun get_field (p:prog) (c:string) (f:string):typ option = 
    let val cls = extract_cls_option (find_class (#prog_clss p) c)
        val field_list = #cls_fields cls 
        
        fun field [] f      = NONE
          | field (x::xs) f = 
            let val (field_name, field_typ) = x
            in
                if field_name = f then
                    SOME field_typ
                else
                    field xs f
            end
    in field field_list f
    end

fun lookup_field (p:prog) (c:string) (f:string):typ = 
    (case built_in c
      of true  => raise Not_found
       | false => 
         (case get_field p c f
           of (SOME x) => x
            | (NONE) => 
               let val cls = extract_cls_option (find_class (#prog_clss p) c)
               in lookup_field p (#cls_super cls) f
               end ))

fun is_subtype (p:prog) (t1:typ) (t2:typ):bool = 
    let fun stringify (TClass s) = s
        val id1 = stringify t1
        val id2 = stringify t2

        fun class s1 s2 = 
            let val cls1 = extract_cls_option (find_class (#prog_clss p) s1)
                val super_s1 = #cls_super cls1
            in 
                if super_s1 = s2 then true else false
            end

        fun trans s1 s2 = 
            let val cls1 = extract_cls_option (find_class (#prog_clss p) s1)
                val cls2 = extract_cls_option (find_class (#prog_clss p) s2)
            in
                if s1 = "Object" then
                    false
                else if class s1 id2 then
                    true
                else
                    trans (#cls_super cls1) id2
            end

        fun subtype s1 s2 = 
            if s1 = s2 then
                true
            else
                (case (s1, s2)
                  of ("Bot", _)    => true
                   | (_, "Bot")    => false
                   | (_, "Object") => true
                   | (_, _)        => trans s1 s2)

    in subtype id1 id2
    end

fun tc_expr (p:prog) (a:env) ((EInt n):expr):typ = TClass "Integer"
  | tc_expr p a ENil = TClass "Bot"
  | tc_expr p a (EString s) = TClass "String"
  | tc_expr p a ESelf = 
    let val option_var = List.find (fn (str, _) => if str = "self" then true else false) a
        val (_, t) = extract_self_option option_var
    in 
        t
    end

  | tc_expr p a (ELocRd s) =
    let val option_var = List.find (fn (str, _) => if str = s then true else false) a
        val (str, t) = extract_id_option option_var
    in 
        t
    end

  | tc_expr p a (EFldRd s) = 
    let val TClass c = tc_expr p a ESelf
        val t = lookup_field p c s
    in
        t
    end 

  | tc_expr p a (EIf (e1, e2, e3)) =
    let val t1 = tc_expr p a e1
        val t2 = tc_expr p a e2
        val t3 = tc_expr p a e3
    in 
        if t2 = t3 then t2 else raise Type_error 
    end 

  | tc_expr p a (ESeq (e1, e2)) =
    let val t1 = tc_expr p a e1
        val t2 = tc_expr p a e2
    in 
        t2
    end

  | tc_expr p a (ELocWr (s, e)) = 
    let
        val t1 = tc_expr p a e 
        val option_var = List.find (fn (str, _) => if str = s then true else false) a
        val (str, t2) = extract_id_option option_var
    in 
        if s = "self" then 
            raise Write_toSelf 
        else 
            if is_subtype p t1 t2 then t2 else raise Type_error
    end

  | tc_expr p a (EFldWr (s,e)) = 
    let val t1 = tc_expr p a e 
        val t2 = tc_expr p a (EFldRd s)
    in
        if is_subtype p t1 t2 then t2 else raise Type_error
    end

  | tc_expr p a (ENew s) =
    if defined_class p s then TClass s else raise Type_error

  | tc_expr p a (ECast (e, t)) = 
    let val t1 = tc_expr p a e
    in 
        t
    end

  | tc_expr p a (EInvoke (e, s, e_list)) =
    let val TClass str = tc_expr p a e
        val t1_list = List.map (fn x => tc_expr p a x) e_list
        val (t2_list, t) = lookup_meth p str s
        val t_list = ListPair.zipEq (t1_list, t2_list)
        val b_list = List.map (fn (t1, t2) => is_subtype p t1 t2) t_list
    in 
        if List.all (fn b => b) b_list then t else raise Type_error 
    end

fun tc_meth (p:prog) (s:string) (m:meth):unit = 
    let val { meth_name   = m_name, 
              meth_ret    = m_ret_type, 
              meth_args   = m_args, 
              meth_locals = m_locals, 
              meth_body   = m_body
            } = m
        val self = [("self", TClass s)]
        val a:env = m_locals @ m_args @ self
        val t_body = tc_expr p a m_body
    in 
        if is_subtype p t_body m_ret_type then () else raise Type_error
    end

fun tc_class (p:prog) (c:cls):unit = 
    if no_builtin_redef p then
        let val { prog_clss = cls_list,
                  prog_main = e } = p
       
            val { cls_name   = c_name,
                  cls_super  = c_super,
                  cls_fields = c_fields,
                  cls_meths  = c_meths } = c
        
        in 
            List.app (fn m => tc_meth p c_name m) c_meths
        end
    else 
        raise Type_error

fun tc_prog (p:prog):unit = 
    let val { prog_clss = cls_list,
              prog_main = e } = p
        val t = tc_expr p [] e

    in 
        List.app (fn c => tc_class p c) cls_list
    end
