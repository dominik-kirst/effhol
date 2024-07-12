nat : Type

term : Type
form : Type

cterm : nat -> (bind term in form) -> term

implies : form -> form -> form
all : nat -> (bind term in form) -> form
holds : term -> term -> form

type : Type
prog : Type
index : Type
exp : Type
spec : Type

app : type -> type -> type
abs : nat -> (bind type in type) -> type
arrow : type -> type -> type
pi : nat -> (bind type in type) -> type
comp : type -> type

tyabs : nat -> (bind type in prog) -> prog
tmabs : type -> (bind prog in prog) -> prog
tyapp : prog -> type -> prog
tmapp : prog -> prog -> prog
ret : prog -> prog
bind : prog -> (bind prog in prog) -> prog

refb : type -> index
ref : type -> index -> index
univ : nat -> (bind type in index) -> index

cexp : type -> index -> (bind exp, prog in spec) -> exp
exabs : nat -> (bind type in exp) -> exp
exapp : exp -> type -> exp

spholds : exp -> exp -> prog -> spec
spimplies : spec -> spec -> spec
after : prog -> (bind prog in spec) -> spec
tyall : nat -> (bind type in spec) -> spec
tmall : type -> (bind prog in spec) -> spec
spall : index -> (bind exp in spec) -> spec
