
sig ID {}

sig A_S {
	var used : set ID ,
	var free : set ID
}

pred A_Inv[s:A_S]
{
	no s.used & s.free
}

pred Used_Init[s:A_S]
{
	no s.used
}

pred Used_Skip[s:A_S] 
{
	s.used' = s.used 
}

pred Used_Add[s:A_S, item:ID] 
{
	s.used' = s.used + item 
}

pred Used_Remove[s:A_S, item:ID] 
{
	s.used' = s.used - item 
}

pred Free_Skip[s:A_S] 
{
	s.free' = s.free
}

pred Free_Init[s:A_S]
{
	s.free = ID // note the difference with Used_Init
}

pred Free_Add[s:A_S, item:ID] 
{
	s.free' = s.free + item 
}

pred Free_Remove[s:A_S, item:ID] 
{
	s.free' = s.free - item
}

// abstract system operations

pred A_Init[s:A_S]
{
	Used_Init[s]
	Free_Init[s]
}

pred A_acquire[s:A_S, item:ID]
{
	item in s.free

	Used_Add[s, item]
	Free_Remove[s, item]
}

pred A_release[s:A_S, item:ID]
{
	item in s.used

	Used_Remove[s, item]
	Free_Add[s, item]
}
	
pred A_dispose[s:A_S, item:ID]
{
	item in s.free

	Used_Skip[s]
	Free_Remove[s, item]
}

pred A_purchase[s:A_S, item:ID]
{
	item !in s.free
	item !in s.used

	Used_Skip[s]
	Free_Add[s, item]
}

pred A_skip[s:A_S]
{
	Free_Skip[s]
	Used_Skip[s]
}

fact {

	A_Init[A_S]

	always
	some item : ID | {

		A_acquire[A_S, item] or 
		A_release[A_S, item] or 
		A_dispose[A_S, item] or 
		A_purchase[A_S, item] 
	}

} 

run { eventually { # A_S.used = 3 } } for 3 but 1 A_S

check {
	always {
		A_Inv[A_S]
	}
} for 3 but 1 A_S



