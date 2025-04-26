open id
open chain

fact {

	Chain_Init[Chain]

	always {
	
		some item : ID - NULL | {

			Chain_Add[Chain, item] or 
			Chain_Remove[Chain, item]
		}
	}

} 

// safety

check { always Chain_Inv[Chain] } for 3 but 1 Chain

// liveness

run { some item : ID - NULL | eventually Chain_Add[Chain, item] } for 3 but 1 Chain

run { some item : ID - NULL | eventually Chain_Remove[Chain, item] } for 5 but 1 Chain
