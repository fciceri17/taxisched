//Signatures

abstract sig Ride{
				start: one Place
}

sig InstantRide extends Ride{
}

sig BookedRide extends Ride{
				destination: one Place,
				depTime: one Time,
				arrTime: one Time
}

sig Place{
}

sig Time{
}
