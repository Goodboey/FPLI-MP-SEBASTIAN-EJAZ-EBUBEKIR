module Mp

// Interpreter & compiler made by groupmembers
// Sebastian Nørager (69391)
// Ebubekir Kayhan (69005)
// Ejaz Ahmad Safi (66473)

(*
________ _______  __       ______
|        \       \|  \     |      \
| ▓▓▓▓▓▓▓▓ ▓▓▓▓▓▓▓\ ▓▓      \▓▓▓▓▓▓
| ▓▓__   | ▓▓__/ ▓▓ ▓▓       | ▓▓
| ▓▓  \  | ▓▓    ▓▓ ▓▓       | ▓▓
| ▓▓▓▓▓  | ▓▓▓▓▓▓▓| ▓▓       | ▓▓
| ▓▓     | ▓▓     | ▓▓_____ _| ▓▓_
| ▓▓     | ▓▓     | ▓▓     \   ▓▓ \
\▓▓      \▓▓      \▓▓▓▓▓▓▓▓\▓▓▓▓▓▓

To Test program: __ "write in console"
#r "parser.dll";;
#r "asm.dll";;
#r "vm.dll";;

To test interpreter: __ "write in console"
Mp.evalProg (Parser.parseProgFromString "--INSERT FUNCTION DEFINITION AND CALL HERE--");;

To test compiler: __ "write in console"
open Asm;;
let test = Mp.comp [] (parseExpFromString "--INSERT EXPRESSION HERE");;
VM.exec (asm test);;

note:

*)

type varname = string
type funcname = string
type func = funcname * (varname * exp)           // func f ( x ) = e

// Environments (interpreter)

type 'a env = (varname * 'a) list

let rec lookup x = function
  | []            -> failwith ("unbound: " + x)
  | (y, w) :: env -> if x = y then w else lookup x env

type value = | VI of int
             | VB of bool

// Interpreter
let evalProg (funcs, e) =
  let rec eval env = function
    | INT i           -> VI i
    | VAR "true"      -> VB true
    | VAR "false"     -> VB false
    | VAR x           -> lookup x env
    | ADD (e1, e2)    -> match (eval env e1, eval env e2) with                    //Arithmetic operations
                         | (VI v1, VI v2)   -> VI(v1+v2)
                         | _                -> failwith ("Not an integer")
    | SUB (e1, e2)    -> match (eval env e1, eval env e2) with
                         | (VI v1, VI v2)   -> VI(v1-v2)
                         | _                -> failwith ("Not an integer")
    | NEG (e1)        -> match (eval env e1) with
                         | (VI v1)          -> VI(- v1)
                         | _                -> failwith ("Not an integer")
    | MUL (e1, e2)    -> match (eval env e1, eval env e2) with
                         | (VI v1, VI v2)   -> VI(v1*v2)
                         | _                -> failwith ("Not an integer")
    | DIV (e1, e2)    -> match (eval env e1, eval env e2) with
                         | (_ , VI 0)       -> failwith ("Cannot divide by zero")
                         | (VI v1, VI v2)   -> VI(v1/v2)
                         | _                -> failwith ("Not an integer")
    | MOD (e1, e2)    -> match (eval env e1, eval env e2) with
                         | (VI v1, VI v2)   -> VI(v1%v2)
                         | _                -> failwith ("Not an integer")
    | EQ (e1, e2)     -> match (eval env e1, eval env e2) with                          // Conditionals
                         | (VI v1, VI v2)   -> VB(if v1 = v2 then true else false)
                         | (VB v1, VB v2)   -> VB(if v1 = v2 then true else false)
                         | _                -> failwith ("Neither an integer nor bool")
    | NEQ (e1, e2)    -> match (eval env e1, eval env e2) with
                         | (VI v1, VI v2)   -> VB(if v1 <> v2 then true else false)
                         | (VB v1, VB v2)   -> VB(if v1 <> v2 then true else false)
                         | _                -> failwith ("Neither an integer nor bool")
    | LT (e1, e2)     -> match (eval env e1, eval env e2) with
                         | (VI v1, VI v2)   -> VB(if v1 < v2 then true else false)
                         | _                -> failwith ("Not an integer")
    | GT (e1, e2)     -> match (eval env e1, eval env e2) with
                         | (VI v1, VI v2)   -> VB(if v1 > v2 then true else false)
                         | _                -> failwith ("Not an integer")
    | LE (e1, e2)     -> match (eval env e1, eval env e2) with
                         | (VI v1, VI v2)   -> VB(if v1 <= v2 then true else false)
                         | _                -> failwith ("Not an integer")
    | GE (e1, e2)       -> match (eval env e1, eval env e2) with
                         | (VI v1, VI v2)   -> VB(if v1 >= v2 then true else false)
                         | _                -> failwith ("Not an integer")
    | IF (e1, e2, e3)   -> match (eval env e1, eval env e2, eval env e3) with           // Conditional statement
                         | (VB v1, VI v2, VI v3)  -> VI(if v1 = true then v2 else v3)
                         | _                -> failwith ("Incomplete if-statement")
    | AND (e1, e2)      -> match (eval env e1, eval env e2) with
                         | (VB v1, VB v2)   -> VB(v1 && v2)
                         | _                -> failwith ("Not a boolean")
    | OR (e1, e2)       -> match (eval env e1, eval env e2) with
                         | (VB v1, VB v2)   -> VB(v1 || v2)
                         | _                -> failwith("Not a boolean")
    | LET (x, e1, e2) -> let v = eval env e1
                         eval ((x, v) :: env) e2
    | CALL (f, e)     -> let (xs, body) = lookup f funcs                                // Function Call
                         let v = List.map (fun a -> eval env a) e
                         eval (List.zip xs v) body
  eval [] e

// Instruction set
// from asm.dll
type label   = string

// Environments (compiler)

type cenv = varname list

let rec varpos x = function
  | []       -> failwith ("unbound: " + x)
  | y :: env -> if x = y then 0 else 1 + varpos x env

// Compiler

let mutable labelCounter = 0
let newLabel _ =
  let this = labelCounter
  labelCounter <- this + 1;
  "L" + string(this)

let rec comp env = function
  | INT i        -> [IPUSH i]

  | ADD (e1, e2) -> comp env         e1 @  // ARITHMETIC OPERATIONS ---
                    comp ("" :: env) e2 @
                    [IADD]

  | SUB (e1, e2) -> comp env         e1 @
                    comp ("" :: env) e2 @
                    [ISUB]

  | MUL (e1, e2) -> comp env         e1 @
                    comp ("" :: env) e2 @
                    [IMUL]

  | DIV (e1, e2) -> comp env         e1 @
                    comp ("" :: env) e2 @
                    [IDIV]

  | MOD (e1, e2) -> comp env         e1 @
                    comp ("" :: env) e2 @
                    [IMOD]

  | NEG (e1)     -> [IPUSH 0]           @
                    comp ("" :: env) e1 @
                    [ISUB]

  | VAR x        -> [ILOAD (varpos x env)]

  | EQ (e1, e2)  -> comp env         e1 @     // Equals Operator
                    comp ("" :: env) e2 @
                    [IEQ]

  | NEQ (e1, e2) -> let _then = newLabel()    // Not Equals Operator
                    let _after = newLabel()
                    comp env         e1 @
                    comp ("" :: env) e2 @
                    [IEQ]               @
                    [IJMPIF _then]      @
                    [IPUSH 1]           @
                    [IJMP _after]       @
                    [ILAB   _then]      @
                    [IPUSH 0]           @
                    [ILAB   _after]

  | LT (e1, e2)  -> comp env         e1 @     // Less Than Operator
                    comp ("" :: env) e2 @
                    [ILT]

  | LE (e1, e2)  -> let _then = newLabel()    // Less Than OR Equal Operator
                    let _after = newLabel()
                    comp env         e1 @
                    comp ("" :: env) e2 @
                    [ILT]               @
                    [IJMPIF _then]      @
                    comp env         e1 @
                    comp ("" :: env) e2 @
                    [IEQ]               @
                    [IJMP _after]       @
                    [ILAB _then]        @
                    [IPUSH 1]           @
                    [ILAB _after]

  | GE (e1, e2) -> let _then = newLabel()     // Greather Than OR Equal Operator
                   let _after = newLabel()
                   comp env         e1 @
                   comp ("" :: env) e2 @
                   [ILT]               @
                   [IJMPIF _then]      @
                   [IPUSH 1]           @
                   [IJMP _after]       @
                   [ILAB   _then]      @
                   [IPUSH 0]           @
                   [ILAB   _after]

  | GT (e1, e2) -> let _then1 = newLabel()    // Greater Than Operator
                   let _after1 = newLabel()
                   comp env         e1 @
                   comp ("" :: env) e2 @
                   [ILT]               @
                   [IJMPIF _then1]     @
                   comp env         e1 @
                   comp ("" :: env) e2 @
                   [IEQ]               @
                   [IJMPIF _then1]     @
                   [IPUSH 1]           @
                   [IJMP _after1]      @
                   [ILAB   _then1]     @
                   [IPUSH 0]           @
                   [ILAB   _after1]

  | LET (x, e1, e2) -> comp env        e1 @     // LET Operator
                       comp (x :: env) e2 @
                       [ISWAP]            @
                       [IPOP]

  | IF (e1, e2, e3) -> let _then  = newLabel()  // IF-THEN-ELSE Operator
                       let _after = newLabel()
                       comp env e1     @
                       [IJMPIF _then]  @
                       comp env e3     @
                       [IJMP   _after] @
                       [ILAB   _then]  @
                       comp env e2     @
                       [ILAB   _after]

  | AND (e1, e2)    -> let _then = newLabel()  // AND Operator
                       let _after = newLabel()
                       let _fail = newLabel()
                       let _pass = newLabel()
                       comp env e1     @
                       [IPUSH 1]       @
                       [IEQ]           @
                       [IJMPIF _then]  @
                       [IJMP _fail]    @
                       [ILAB _then]    @
                       comp env e2     @
                       [IPUSH 1]       @
                       [IEQ]           @
                       [IJMPIF _pass]  @
                       [IJMP _fail]    @
                       [ILAB _pass]    @
                       [IPUSH 1]       @
                       [IJMP _after]   @
                       [ILAB _fail]    @
                       [IPUSH 0]       @
                       [ILAB _after]

  | OR (e1, e2)    -> let _after = newLabel() // OR operator
                      let _fail = newLabel()
                      let _pass = newLabel()
                      comp env e1     @
                      [IPUSH 1]       @
                      [IEQ]           @
                      [IJMPIF _pass]  @
                      comp env e2     @
                      [IPUSH 1]       @
                      [IEQ]           @
                      [IJMPIF _pass]  @
                      [IJMP _fail]    @
                      [ILAB _pass]    @
                      [IPUSH 1]       @
                      [IJMP _after]   @
                      [ILAB _fail]    @
                      [IPUSH 0]       @
                      [ILAB _after]

  | CALL (f, es)   -> let rec compArgs = function // Function calls, (not finished)
                                  | [] -> []
                                  | e :: es -> comp env e @
                                               compArgs es
                      compArgs es            @
                      //We didn't manage to solve this
                      [ICALL f]              @
                      [ISWAP]                @
                      [IPOP]


// This doesn't work properly
let rec compProg = function
  | ([],                   e1) -> comp [] e1 @
                                  [IHALT]
  | ((f, (x, e)) :: funcs, es) ->  compProg (funcs, es)    @
                                   [ILAB f]                @
                                   comp x e                @
                                   [ISWAP]                 @
                                   [IRETN]



// parseTypedProgFromString "let x = true in x*x";;
// val it : typedfunc list * exp =
// ([], LET ("x", VAR "true", MUL (VAR "x", VAR "x")))
// Mp.compProg (([("yaa", (["x"; "y"], SUB (VAR "x", VAR "y")))], CALL ("yaa", [INT 2; INT 1])));;
