module monopoly

open util/ordering [State] as ord

sig State {}

abstract sig Player {	
	token: one Token, 
	money: set Money,
	ownedProperties: some Property,
	ownedUtilities: some Utilities,
	ownedRailroads: some Railroad,
	houses: Property -> House,
	hotels: Property -> Hotel 
}

abstract sig Location{
	Price: one Price
}

abstract sig Building {
	price: Price
}


one sig Board{
	players: some Player,
	properties: some Property
}

sig Token {}
sig Money {}
sig Price {}

sig Property extends Location{
	houses: set House,
	hotels: lone Hotel
}

sig Utilities extends Location{}
sig Railroad extends Location{}


sig Hotel extends Building {}
sig House extends Building {}







run {}
