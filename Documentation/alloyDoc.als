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
				itenerary: set Place
}

sig Place{
}

sig User{
}

sig TaxiDriver{
}

//FACTS

fact DriverBounds{
//Every TaxiDriver can't have more than one ride assigned
no disj r1, r2: Ride | r1.driver=r2.driver
//In shared rides, the driver must be same for every part of the itinerary
all sr: SharedRide | (no disj br1, br2: BookedRide | br1 in sr.components and br2 in sr.components and br1.driver != br2.driver)
}

fact NewReservation{
//A User can't make more than one reservation in a certain period of time
no disj br1, br2: BookedRide | (br1.mainPassanger = br2.mainPassenger and (br1.depTime-br2.depTime < 30 and br2.depTime-br1.depTime < 30)  


fact RideBounds{
//The starting position and the arriving position can't be the same
all br: BookedRide | !(br.start=br.destination) 
//In shared ride, the itinerary must be composed by all the places that are either a starting or a destination point of a booked ride that composes the sharing
all sr: SharedRide | all br: BookedRide | br in sr.composition implies (br.start in sr.itinerary and br.destination in sr.itinerary)
//In shared ride, the itinerary must be composed by only the places that are either a starting or a destination point of a booked ride that composes the sharing
all sr: SharedRide | (all p: sr.itinerary | (one sp: sr.components.start | sp = p) or (one ap: sr.components.destination | ap = p)) 
}

//ASSERTIONS

//Check that each ride has only one Taxi Driver
assert NoMoreThanOneDriver{
all td: TaxiDriver | (one r: Ride | r.driver=td implies (no r2: Ride | r != r2 and r2.driver=td))
}
check NoMoreThanOneDriver

//PREDICATES

pred showRide{
some br: BookedRide, u: User, td: TaxiDriver | br.mainPassenger = u and br.driver = td
}

run showRide

