
open id
open chain

sig C_S {
	used : Chain ,
	free : Chain
}

fun Used_items[s:C_S] : set ID
{
	Chain_items[s.used]
}

pred Used_Init[s:C_S]
{
	Chain_Init[s.used]
}

pred Used_Skip[s:C_S] 
{
	Chain_Skip[s.used]
}

pred Used_Add[s:C_S, item:ID] 
{
	Chain_Add[s.used, item] 
}

pred Used_Remove[s:C_S, item:ID] 
{
	Chain_Remove[s.used, item]
}

fun Free_items[s:C_S] : set ID
{
	Chain_items[s.free]
}

pred Free_Skip[s:C_S] 
{
	Chain_Skip[s.free]
}

pred Free_Init[s:C_S]
{
	Chain_Full[s.free] // note the difference with Used_Init
}

pred Free_Add[s:C_S, item:ID] 
{
	Chain_Add[s.free, item] 
}

pred Free_Remove[s:C_S, item:ID] 
{
	Chain_Remove[s.free, item]
}

// system invariant

pred C_Inv[s:C_S]
{
	no Used_items[s] & Free_items[s]

	Chain_Inv[s.used]
	Chain_Inv[s.free]
}

// system operations

pred C_Init[s:C_S]
{
	Used_Init[s]
	Free_Init[s]
}

pred C_acquire[s:C_S, item:ID]
{
	item in Free_items[s]

	Used_Add[s, item]
	Free_Remove[s, item]
}

pred C_release[s:C_S, item:ID]
{
	item in Used_items[s]

	Used_Remove[s, item]
	Free_Add[s, item]
}
	
pred C_dispose[s:C_S, item:ID]
{
	item in Free_items[s]

	Used_Skip[s]
	Free_Remove[s, item]
}

pred C_purchase[s:C_S, item:ID]
{
	item !in Free_items[s]
	item !in Used_items[s]

	Used_Skip[s]
	Free_Add[s, item]
}

fact {

	C_Init[C_S]

	always
	some item : ID | {

		C_acquire[C_S, item] or 
		C_release[C_S, item] or 
		C_dispose[C_S, item] or 
		C_purchase[C_S, item] 
	}

} 

// safety

check {
	always {
		C_Inv[C_S]
	}
} for 3 but 1 C_S

// liveness

run { eventually { # Used_items[C_S] = 2 } } for 4 but 1 C_S



 
