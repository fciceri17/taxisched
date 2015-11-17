//Signatures

abstract sig Ride{
				start: one Place,
				driver: one TaxiDriver
}

sig InstantRide extends Ride{
}

sig BookedRide extends Ride{
				mainPassenger: one User,
				occupation: one Int,
				destination: one Place,
				depTime: one Int
}

sig SharedRide {
				components: set BookedRide,
				itinerary: set Place
}

sig Place{
}

sig User{
}

sig TaxiDriver{
}



//FACTS

//depTime can't be negative
fact NoNegativeTime{
all br: BookedRide | br.depTime >=0
}

//occupation must be at least one
fact NoNullPassenger{
all br: BookedRide | br.occupation > 0
}

fact DriverBounds{
//Every TaxiDriver can't have more than one ride assigned, unless they are componing the same shared ride
all td: TaxiDriver | all disj r1, r2: Ride | assignRide [r1, td] implies (r2.driver !=td or one sr: SharedRide | r1 in sr.components and r2 in sr.components) 
//In shared rides, the driver must be same for every part of the itinerary
all sr: SharedRide | all disj br1, br2: BookedRide | (br1 in sr.components and br2 in sr.components) implies br1.driver = br2.driver
}

fact NewReservation{
//A User can't make more than one reservation in a certain period of time
no disj br1, br2: BookedRide | (br1.mainPassenger = br2.mainPassenger and !(br1.depTime-br2.depTime < 30 and br2.depTime-br1.depTime < 30))
}



fact RideBounds{
//
//The starting position and the arriving position can't be the same
all br: BookedRide | !(br.start=br.destination) 
//In shared rides, the itinerary must be composed by all the places that are either a starting or a destination point of a booked ride that composes the sharing
all sr: SharedRide | all br: BookedRide | br in sr.components implies (br.start in sr.itinerary and br.destination in sr.itinerary)
//In shared rides, the itinerary must be composed by only the places that are either a starting or a destination point of a booked ride that composes the sharing
all sr: SharedRide | (all p: Place | p in sr.itinerary implies (one rp: Place | (rp in sr.components.start and rp = p) or (rp in sr.components.destination and rp = p))) 
//In shared rides,all the components must have a different mainPassenger
all sr: SharedRide | no disj br1, br2: BookedRide | ( br1 in sr.components and br2 in sr.components and br1.mainPassenger = br2.mainPassenger)
//Every shared rides must have at least one component
all sr: SharedRide | #sr.components>0
//Two shared rides can't share the same booked ride as a component
all sr: SharedRide | all br: BookedRide | br in sr.components implies all sr2: SharedRide | br in sr2.components implies sr2=sr
//In shared rides, two components can start at the same place if and only if they start at the same time
all sr: SharedRide | all disj br1, br2: BookedRide | (br1 in sr.components and br2 in sr.components) implies (br1.depTime = br2.depTime iff br1.start = br2.start)
}


//ASSERTIONS

//Check that each ride has only one Taxi Driver
assert NoMoreThanOneDriver {
all disj td1, td2: TaxiDriver | all r: Ride | (r.driver = td1 implies r.driver != td2) and (r.driver = td2 implies r.driver != td1)
}
check NoMoreThanOneDriver for 5	

//Check that when a ride is added to a Shared Ride, it is contained in the components
assert CorrectCompose {
all br: BookedRide | all sr: SharedRide | (composeRide [br,sr] implies br in sr.components)
}
check CorrectCompose for 5

//Check that there are not two ride with the same main passenger in the same shared ride
assert NoSameMainPassenger{
all disj br1, br2: BookedRide | br1.mainPassenger = br2.mainPassenger implies no sr: SharedRide | br1 in sr.components and br2 in sr.components
}
check NoSameMainPassenger for 5

//Check that there can't be two rides created by the same user that have departure time closer that 30 minutes
assert NoTooCloseRide{
all disj br1, br2: BookedRide | br1.mainPassenger = br2.mainPassenger implies (br1.depTime-br2.depTime > 30 or br2.depTime-br1.depTime > 30)
}
check NoTooCloseRide for 5

//Check that if a booked ride composes a shared ride, its starting and arriving place are in the shared's itinerary
assert ConsistentItinerary{
all sr: SharedRide | all br: BookedRide | (br in sr.components implies (br.start in sr.itinerary and br.destination in sr.itinerary))
}
check ConsistentItinerary for 5

//Check that a booked ride can't be in the composition of more that of shared ride
assert NoMoreThanOneSharedComponent {
all br: BookedRide | all sr: SharedRide | (br in sr.components implies (no sr2: SharedRide | sr!=sr2 and br in sr2.components))
}
check NoMoreThanOneSharedComponent for 5


//PREDICATES

pred show(){
#InstantRide>1
#BookedRide>1
#SharedRide>1
#User>1
#TaxiDriver>1
#Place>1 }
run show for 5

//Pred to show the relationship between bookied rides, shared rides, places and drivers
pred showSharing(){
#BookedRide > 1
#components >3
#SharedRide = 1
#User >3
#TaxiDriver > 1
#InstantRide = 0
#mainPassenger > 1
#Place > 1 }
run showSharing for 5

//Pred to show the relationship and the differencies between booked and instant rides
pred showRides(){
#BookedRide >1
#InstantRide >1
#SharedRide = 0 }
run showRides for 5

//Pred to assing a ride to a taxi driver
pred assignRide (r: Ride, td: TaxiDriver){r.driver = td}
run assignRide for 5

//Pred to add a ride to a shared ride
pred composeRide (br: BookedRide, sr: SharedRide) {br in sr.components and br.start in sr.itinerary and br.destination in sr.itinerary}
run composeRide for 5
