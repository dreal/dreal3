(*
 * Soonho Kong, soonhok@cs.cmu.edu
 * Static Array Elimination Pass
 *)

open Pretty
open Cil
open Rtcbautil

module E = Errormsg
module H = Hashtbl

(** Aux operator to create a range:
 **      # 5--10;;
 **      - : int list = [5; 6; 7; 8; 9]   
 **)
let (--) i j = 
  let rec range i j = if i >= j then [] else i :: (range (i+1) j) in
  range i j

let makeName str n = str ^ "_" ^ (string_of_int n)
    
(**
   `collectDeclVisitor` collects static array definitions which
   satisfy `elimCond` predicates. It updates the `arrayTable`
   hashtable which maps an arrayName into a pair of its element type
   and the length of an array.
**)
class collectDeclVisitor 
  (elimCond  : varinfo -> bool) 
  (arrayTable: (string, (typ * int)) H.t)
  = object(self)
    inherit nopCilVisitor
    method vvdec (v : varinfo) : varinfo visitAction = 
      match v.vtype with
          (* Only consider an array type whose size can be determined
             in static time *)
          TArray (ty, e_opt, attr) when elimCond(v) ->
            begin 
              try
                let n = lenOfArray e_opt in
                H.add arrayTable v.vname (ty, n);
                DoChildren
              with LenOfArray -> DoChildren
            end
        (* ignore others *)
        | _ -> DoChildren
  end

(** 
    `staticReplaceVisitor` does the first pass of the static array
    elimination process by doing:

    1. Replace arr[<exp>] with arr_<n>
       if <exp> can be evaluated to <n> in static time 
    2. Replace sizeof(arr) with its length * sizeof(T)
       where T is the type of the element of arr

    Note that it does not handle array accesses whose index
    expressions need to be evaluated in the run-time. They are left
    for `nonStaticReplaceVisitor`.
**)
class staticReplaceVisitor
  (arrayTable: (string, (typ * int)) H.t)
  (varTable  : (string, varinfo) H.t)
  = object(self)
    inherit nopCilVisitor
    (*  1. arr[0] => arr_0 *)
    method vlval (vl : lval) : lval visitAction 
      = match vl with
          (Var vinfo, Index (e, NoOffset))
            when H.mem arrayTable vinfo.vname->
              begin 
                try
                  let n = lenOfArray (Some e) in
                  let vname' = makeName vinfo.vname n in
                  let vinfo' = H.find varTable vname' in
                  ChangeTo (Var vinfo', NoOffset)
                with LenOfArray -> DoChildren
              end
        | _ -> DoChildren
            
    (* sizeof(arr) => sizeof(elt) * len *)
    method vexpr (e : exp) : exp visitAction
      = match e with
          SizeOfE(Lval(Var arr, NoOffset))
            when H.mem arrayTable arr.vname
              -> let (ty, n) = H.find arrayTable arr.vname in 
                 ChangeTo (BinOp (Mult,
                                  SizeOf ty,
                                  integer n,
                                  Cil.intType))
        | _ -> DoChildren
  end

(**
   `nonStaticReplaceVisitor` is the 2nd pass of the static array
   elimination process. It handles the following cases:

   Case 1: arr[idx_e] = e; 
       =>  setFn (idx_e, e)

   
   Case 2: v = arr[idx_e];
       =>  tmpVar = getFn(idx_e);
           v = tmpVar;

   Case 3: f (arr[idx_e]);
       =>  tmpVar = getFn(idx_e);
           f ( tmpVar )

   It creates array accessor functions (get_...) when it is required
   and updates `getFnTable` hashtable which maps an array to its
   accessor function.

**)
class nonStaticReplaceVisitor
  (arrayTable: (string, (typ * int)) H.t)
  (varTable  : (string, varinfo) H.t)
  (getFnTable: (string, fundec) H.t)
  (setFnTable: (string, fundec) H.t)
  (dieFn : varinfo)
  = object(self)
    (* Need to keep track of the current function to create temp variables *)
    val mutable curFundec = dummyFunDec
    inherit nopCilVisitor

    method vfunc (fd : fundec) : fundec visitAction
      = (curFundec <- fd); DoChildren

    method vinst (i : instr) : instr list visitAction
      = 
      let createSetFn (name : string) =
	  if H.mem setFnTable name then H.find setFnTable name
	  else
	    begin
	      let (ty, n) = H.find arrayTable name in
	      let setFnName = "__startrek_ar_set_" ^ name in
	      let setFn = emptyFunction setFnName in
	      let setFnType = TFun (Cil.voidType,
				    Some [],
				    false, []) in
	      setFunctionTypeMakeFormals setFn setFnType;
	      let kVar = makeFormalVar setFn "k" Cil.uintType in
	      let eVar = makeFormalVar setFn "e" ty in
	      let dieLv = Lval (var dieFn) in
	      let call = Call (None, dieLv, [], builtinLoc) in
              let switchStmt =
		mkSwitchStmt (Lval (var kVar)) 0 n
		  (fun i ->
                    let ithVarName = name ^ "_" ^ string_of_int(i) in
		    let ithVar = H.find varTable ithVarName in
		    let set = Set (var ithVar, Lval (var eVar), builtinLoc) in
		    [mkStmtOneInstr set ; mkStmt (Break builtinLoc)])
		  ~d:[mkStmtOneInstr call]
	      in
	      setFn.sbody <- mkBlock [switchStmt]; 
	      H.add setFnTable name setFn;
	      setFn
	    end in

      (** Create an instruction with temp variable:
          "T* tempVar = getFn (idx_exp);"
      **)
    let createTempGetInstr arrName tmpVar idx_e loc =
        let createGetFn (name : string) (ty : typ) (n : int) =
          (* create get function for an array *)
          let getFnName : string = "__startrek_ar_get_" ^ name in
          let getFn : fundec = emptyFunction getFnName in
          let getFnType : typ = TFun (ty,
                                      Some [],
                                      false,
                                      []) in
          setFunctionTypeMakeFormals getFn getFnType;
          let kVar = makeFormalVar getFn "k" Cil.uintType in
	  let dieLv = Lval (var dieFn) in
	  let call = Call (None, dieLv, [], builtinLoc) in	  
          let switchStmt =
            mkSwitchStmt (Lval (var kVar)) 0 n
              (fun i ->
                let ithVarName = name ^ "_" ^ string_of_int(i) in
		let ithVar = H.find varTable ithVarName in
		let ret = Return (Some (Lval (var ithVar)), builtinLoc)
		in [mkStmt ret])

	      (** XXX Should call die(). This is unreachable *)
	      ~d:[mkStmtOneInstr call]
          in
          getFn.sbody <- mkBlock [switchStmt];
          getFn
        in
        let getFn = 
	  if H.mem getFnTable arrName then
            H.find getFnTable arrName
	  else
	    begin 
              let (ty, n) = H.find arrayTable arrName in
              let getFn = createGetFn arrName ty n in
              H.add getFnTable arrName getFn;
              getFn
	    end
        in
        Formatcil.cInstr "%v:tmpVar = %v:getFn(%e:idx_e); "
          loc
          [("tmpVar", Fv tmpVar);
           ("getFn", Fv getFn.svar);
           ("idx_e", Fe idx_e);
          ]
      in            
      match i with
          (* Case: arr[idx_e] = e; *)
          Set((Var arr, Index(idx_e, NoOffset)), e, loc) 
            when H.mem arrayTable arr.vname
              -> let arrName = arr.vname in 
		 let setFnFd = createSetFn arrName in
		 let setFn = setFnFd.svar in
		 ChangeTo
		   [Call (None, Lval (var setFn), [idx_e; e], builtinLoc)]
        (* Case: v = arr[idx_e]; *)
        | Set((Var v, NoOffset), Lval(Var arr, Index(idx_e, NoOffset)), loc) 
            when H.mem arrayTable arr.vname
              -> let arrName = arr.vname in 
                 let (ty, n) = H.find arrayTable arrName in 
                 let tmpVar = makeTempVar curFundec ty in
                 let i1 = createTempGetInstr arrName tmpVar idx_e loc in
                 let i2 = 
                   Formatcil.cInstr "%v:v = (%v:tmpVar);"
                     loc
                     [("tmpVar", Fv tmpVar);
                      ("v", Fv v);
                     ]
                 in              
                 ChangeTo [i1;i2]   
        (* Case: f (arr[idx_e]); *)
        | Call(None, 
               Lval(Var f, NoOffset), 
               [Lval(Var arr, Index(idx_e, NoOffset))], 
               loc)
            when H.mem arrayTable arr.vname
              -> let arrName = arr.vname in 
                 let (ty, n) = H.find arrayTable arrName in 
                 let tmpVar = makeTempVar curFundec ty in
                 let i1 = createTempGetInstr arrName tmpVar idx_e loc in
                 let i2 = 
                   Formatcil.cInstr "%v:f (%v:tmpVar);"
                     loc
                     [("tmpVar", Fv tmpVar);
                      ("f", Fv f);
                     ]
                 in              
                 ChangeTo [i1;i2]   
        | Asm _ -> DoChildren
        | _ -> DoChildren
  end
  
(** Only do the elimination 
    if the array name starts with "__startrek_" **)
let elimCond (v : varinfo) : bool 
    = startsWith "_" v.vname

(** Main Loop **)
let doit (fl: file) = 

  (* 0. create die() function, the semantics of die() is assume(0) *)
  let dieFnTy = TFun (Cil.voidType, None, false, []) in
  let dieFn = 
    let dieFn' = makeGlobalVar "__startrek_unreach" dieFnTy in
    let dieFd = GVarDecl (dieFn', builtinLoc) in
    dieFn'.vattr <- [Attr ("noreturn", [])] ;
    dieFn'.vstorage <- Extern ;
    fl.globals <- dieFd :: fl.globals ; dieFn'
  in
  (* 1. Collect Array Information *)
  (* arrayTable : NameOfArray => Type and Size *)
  let arrayTable: (string, (typ * int)) H.t = H.create 5 in
  (* varName    : NameOfnewVar => its varinfo *)
  let varTable: (string, varinfo) H.t = H.create 5 in
  let getFnTable: (string, fundec) H.t = H.create 5 in
  let setFnTable: (string, fundec) H.t = H.create 5 in
  let cdvisitor = (new collectDeclVisitor elimCond arrayTable) in
  visitCilFile cdvisitor fl;
  (* 2. Create New Declarations *)
  let newGlobals = 
    foldGlobals fl
      (fun gs g -> 
        match g with 
            GVarDecl (vinfo, loc)
              when H.mem arrayTable vinfo.vname -> 
                (* In case of VarDecl, we just delete the decl
                   without creating new variables*)
                gs
          | GVar (vinfo, initinfo, loc)
              when H.mem arrayTable vinfo.vname -> 
              let name = vinfo.vname in
            (* In case of Var, 
               1. we delete the GVar and
               2. create variables for that array*)
              let (ty, n) = H.find arrayTable name in
              let vars : global list =
                begin
                  match initinfo.init with
		    (* In case the array is initialzed with init list,
		       we add those values into variable declarations *)
		    | Some (CompoundInit (eltTy, offset_init_list)) ->
                      List.map2
                        (fun k (o, i) ->
                          let varName = makeName name k in
                          let var = makeGlobalVar varName ty in
                          H.add varTable varName var;
                          GVar (var,
                                {init = Some i},
                                builtinLoc)
                        )
                        (0 -- n)
                        offset_init_list
                    (* Otherwise, just create variable declarations
                       without init info *)
                    | Some (SingleInit _) | None -> 
		      List.map
                        (fun k ->
                          let varName = makeName name k in
                          let var = makeGlobalVar varName ty in
                          H.add varTable varName var;
                          GVar (var,
                                {init = None},
                                builtinLoc)
                        )
                      (0 -- n)
                end
              in
              (* 3. create an emptyFunction as a placeholder for the
                 accessor function. This emptyfunction will be either
                 A) deleted in case all the accesses are static
                 accesses or B) replaced with the actual accessor
                 function. *)
              gs @ vars @ [GFun (emptyFunction vinfo.vname, builtinLoc)]
          | _ -> gs @ [g]
      )
      [] 
  in
  fl.globals <- newGlobals;
  (* Run 1st pass *)
  visitCilFile (new staticReplaceVisitor arrayTable varTable) fl;
  (* Run 2st pass *)
  visitCilFile (new nonStaticReplaceVisitor 
		  arrayTable varTable getFnTable setFnTable dieFn) fl;
  (* Process `emptyFunction`s created before *)
  fl.globals <- foldGlobals fl
    (fun gs g ->
      match g with
          GFun(fd, loc) when H.mem arrayTable fd.svar.vname ->
            let arrName = fd.svar.vname in
            begin
              let gs' = if H.mem getFnTable arrName then
                  let getFn = H.find getFnTable arrName in
                  gs @ [GFun (getFn, builtinLoc)]
		else gs in

	      if H.mem setFnTable arrName then
		let setFn = H.find setFnTable arrName in
		gs' @ [GFun (setFn, builtinLoc)]
	      else gs'
            end

	| _ -> gs @ [g]
    )
    []
    
(* command line option for first pass *)
let feature : featureDescr = { 
  fd_name = "sae";              
  fd_enabled = ref false;
  fd_description = "Static Array Elimination";
  fd_extraopt = [];
  fd_doit = doit;
  fd_post_check = true;
}
