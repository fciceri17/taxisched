//Signatures

abstract sig Ride{
				start: one Place,
				driver: one TaxiDriver
}

sig InstantRide extends Ride{
}

sig BookedRide extends Ride{
				mainPassenger: one User,
				destination: one Place,
				depTime: one Time,
				arrTime: one Time
}

sig SharedRide extends BookedRide{
				joiningPass: set User
}
sig Place{
}

sig Time{
}

sig User{
}

sig TaxiDriver{
}


//FACTS

fact OneRidePerDriver{
//Every TaxiDriver can't have more than one ride assigned
no disj r1, r2: Ride | r1.driver=r2.driver
}

fact JoinSharedRides{
//The creator of the Ride can't join it
all sr: SharedRide | (no jp: sr.joiningPass | jp = sr.mainPassenger)
//Users can't join a Ride which they have already joined
all sr: SharedRide | (no jp1, jp2: sr.joiningPass | jp1 = jp2)
//Users can join a Ride only if they haven't booked a Ride which is scheduled at the same time
 
}

fact RideBounds{
//The starting position and the arriving osition can't be the same
all br: BookedRide | !(br.start=br.destination) 
//The departuring time must be before the arriving time
all br: BookedRide | br.depTime < br.arrTime
}

fact 

