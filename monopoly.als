module monopoly

open util/ordering [State] as ord

// ----------------------- SIGNATURES ----------------------- //
sig State {}
sig Dice {}

// Board sig has Players and Spaces which are Locations
one sig Board{
	players: some Player,
	spaces: some Location
}

// Player sig
some sig Player {	
	token: one Token, 
	money: set Money,
	ownedProperties: one OwnedProperties,
	ownedUtilities: one OwnedUtilities,
	ownedRailroads: one OwnedRailroads,
}

// Tokens are unique to each player
sig Token {}{ one this.~token }

// Abstract sig representing a purchasable signature
abstract sig Purchasable{ price: one Price }
abstract sig Location extends Purchasable {}
abstract sig Building extends Purchasable {}
sig Money {}

// Prices are unique
sig Price {}{ one this.~price }

// Property is a Location which can have Houses or up to one Hotel
sig OwnedProperties { 
	properties: set Property,
 	houses: Property->House,
	hotels: Property->Hotel
}
sig Property extends Location{
	houses: set House,
	hotels: lone Hotel
}
sig Hotel extends Building {}
sig House extends Building {}

// Utilities and Railroads are Locations with a Price
sig OwnedUtilities { utilities: set Utilities }
sig Utilities extends Location{}
sig OwnedRailroads { railroads: set Railroad }
sig Railroad extends Location{}

// Die sig contains values to be rolled
//sig Die{ values: set Values }
//sig Values{}

// Each game has a Banker
//one sig Banker extends Player{}
// ----------------------- SIGNATURES ----------------------- //

// ----------------------- FACTS ----------------------- //
pred init (p: Player) {
	no p.ownedProperties.properties
	no p.ownedUtilities.utilities
	no p.ownedRailroads.railroads
}

fact boardOwnedStacks {
	all b: Board | #b.players.ownedProperties = #b.players
	all b: Board | #b.players.ownedRailroads = #b.players
	all b: Board | #b.players.ownedUtilities = #b.players
}

// If two Players have the same Properties, then they are the same Player
fact uniqueProperties { 
	no disj p, p': Player | p.ownedProperties = p'.ownedProperties
	no disj p, p': Player | p.ownedProperties.properties = p'.ownedProperties.properties
}
fact oneOwnedProperty { 
	all p: Player | one p.ownedProperties
}

// If two Players have the same Utilities, then they are the same Player
fact uniqueUtilities { 
	no disj p, p': Player | p.ownedUtilities = p'.ownedUtilities
//	no disj p, p': Player | p.ownedUtilities.utilities = p'.ownedUtilities.utilities
}
fact oneOwnedUtility { 
	all p: Player | one p.ownedUtilities
}

// If two Players have the same Railroads, then they are the same Player
fact uniqueRailroads { 
	no disj p, p': Player | p.ownedRailroads = p'.ownedRailroads
//	no disj p, p': Player | p.ownedRailroads.railroads = p'.ownedRailroads.railroads 
}
fact oneOwnedRailroad { 
	all p: Player | one p.ownedRailroads
}

// If two Players have the same Money, then they are the same Player
fact uniqueMoney { 
	no disj p, p': Player | p.money = p'.money
}

// Players only have one money balance
fact oneBalance { 
	all p: Player | one p.money 
}

// Players only have one money balance
fact oneSetofProperties { 
	all p: Player | one p.ownedProperties
}

// A Player cannot have a Hotel without 4 Houses
fact needFourHouses { 
	all p: Player | #p.ownedProperties.houses < 4 implies #p.ownedProperties.hotels = 0
}

// Players are on the Board
fact allPlayersOnBoard{
	all p: Player | one b:Board | p in b.players
}

// Spaces are on the Board
fact allSpacesOnBoard{
	all l: Location | one b:Board | l in b.spaces
}
// ----------------------- FACTS ----------------------- //

// ----------------------- FUNCTIONS ----------------------- //

// Returns all of the owned Locations on the board
fun allOwnedLocations[b: Board] : set Location {
	b.players.ownedProperties.properties + b.players.ownedUtilities.utilities + b.players.ownedRailroads.railroads
}
pred ownRailroad[b: Board, r: Railroad] {
	r in allOwnedLocations[b]
}
pred ownUtility[b: Board, u: Utilities] {
	u in allOwnedLocations[b]
}
pred ownProperty[b: Board, p: Property] {
	p in allOwnedLocations[b]
}
//run ownRailroad
//run ownUtility
//run ownProperty

// Return all of a player's owned properties 
fun playerProperties[p: Player] : set Property {
	p.ownedProperties.properties
}
// Return all of a player's owned railroads 
fun playerRailroads[p: Player] : set Railroad {
	p.ownedRailroads.railroads
}
// Return all of a player's owned utilities 
fun playerUtilities[p: Player] : set Utilities {
	p.ownedUtilities.utilities
}
// Ensures that if a player owns properties, they appear in the owned properties and that that player only
// has one set of owned properties
fact oneStackButManyOwnedProp {
	all p: Player | some p.ownedProperties.properties implies some playerProperties[p] && one p.ownedProperties
}
// Ensures that if a player owns railroads, they appear in the owned railroads and that that player only
// has one set of owned railroads
fact oneStackButManyOwnedRail {
	all p: Player | some p.ownedRailroads.railroads implies some playerRailroads[p] && one p.ownedRailroads
}
// Ensures that if a player owns utilities, they appear in the owned utilities and that that player only
// has one set of owned utilities
fact oneStackButManyOwnedUtil {
	all p: Player | some p.ownedUtilities implies some playerUtilities[p] && one p.ownedUtilities
}
// Multiple players cannot own the same utility
fact onePlayerOwnsUtility {
//	all p, p': Player, u: Utilities | u in playerUtilities[p] implies !(u in playerUtilities[p'])
}

// Returns all properties on the board
fun propertiesOnBoard[b: Board] : set Property {
	b.players.ownedProperties.properties
}
// Returns all railroads on the board
fun railroadsOnBoard[b: Board] : set Railroad {
	b.players.ownedRailroads.railroads
}
// Returns all utilities on the board
fun utilitiesOnBoard[b: Board] : set Utilities {
	b.players.ownedUtilities.utilities
}
// Board space restraints 
fact playerOwnsAtMost {
	all p: Player |  #playerUtilities[p] >= 0 && #playerUtilities[p]  <= 2
	all p: Player |  #playerRailroads[p] >= 0 && #playerRailroads[p]  <= 4
	all p: Player |  #playerProperties[p] >= 0 // && #playerProperties[p]  <= 22
	all b: Board |  #propertiesOnBoard[b] >= 0 //&& #propertiesOnBoard[b]  <= 22
	all b: Board |  #railroadsOnBoard[b] >= 0 && #railroadsOnBoard[b]  <= 4
	all b: Board |  #utilitiesOnBoard[b] >= 0 && #utilitiesOnBoard[b]  <= 2
}

// Return houses at a property
fun lookUpHouses[p: Player, pr: Property] : set House {
	p.ownedProperties.houses[pr]
}
fact everyHouseMapped {
	all p: Player, pr: Property | some p.ownedProperties.houses implies some lookUpHouses[p, pr]
}

// Return the hotel at a property or empty set if there is not a hotel
fun lookUpHotels[p: Player, pr: Property] : set Hotel {
	p.ownedProperties.hotels[pr]
}
fact everyHotelMapped {
	all p: Player, pr: Property | some p.ownedProperties.hotels implies some lookUpHotels[p, pr]
}
// ----------------------- FUNCTIONS ----------------------- //

// ----------------------- ASSERTIONS ----------------------- //
// Preforming a second acquireProperty has no effect
assert twoIdenticalAcquire {
	all p, p', p'': Player, pr: Property | acquireProperty [p, p', pr] and acquireProperty [p', p'', pr] => p' = p''
}
//check twoIdenticalAcquire

//Checks that all players have a token
assert playerHasAToken {
	
}

//Checks that all players start with one money stack
assert playerHasOneMoneyStack {
	
}

//Confirm that all owned locations are actual locations on the board
assert allOwnedLocationsOnBoard {
	one b:Board | allOwnedLocations[b] in b. spaces
}

//Confirm that all properties are in ownedlocations
assert playersPropertiesAreInOwned{
	one b: Board | all p: Player | (playerProperties[p] + playerRailroads[p] + playerUtilities[p]) in allOwnedLocations[b] 
}

//Checks that all players start with no locations
assert PlayerHasNoLocations {
	all p: Player, pr: Property | 
			init[p] => !(pr in p.ownedProperties.properties)
}
//check PlayerHasNoLocations

// ----------------------- ASSERTIONS ----------------------- //

// ----------------------- DYNAMIC ----------------------- //
//------
pred acquireProperty[p, p': Player, pr: Property] {
	p'.ownedProperties.properties = p.ownedProperties.properties ++ pr
}
// If a property is bought, check that the relation is updated
assert checkAcquireProperty {
	all p, p': Player, pr: Property | !(pr in p.ownedProperties.properties) implies acquireProperty[p, p', pr] => pr in p'.ownedProperties.properties
}
//check checkAcquireProperty for 22
//run acquiringProperties {
//	some p, p': Player, pr: Property | acquireProperty[p, p', pr]
//} for 3 but 8 Player

pred sellProperty[p, p': Player, pr: Property] {
	#p.ownedProperties.properties > 0
	p'.ownedProperties.properties = p.ownedProperties.properties - pr
}
// If a property is sold, check that the relation is updated
assert checkSellingProperty {
	all p, p': Player, pr: Property | pr in p.ownedProperties.properties implies sellProperty[p, p', pr] => !(pr in p'.ownedProperties.properties)
}
//check checkSellingProperty 
//------
//------
pred acquireRailroad[p, p': Player, r: Railroad] {
	p'.ownedRailroads.railroads = p.ownedRailroads.railroads ++ r
}
// If a property is bought, check that the relation is updated
assert checkAcquireRailroad {
	all p, p': Player, r: Railroad | !(r in p.ownedRailroads.railroads) implies acquireRailroad[p, p', r] => r in p'.ownedRailroads.railroads
}
//check checkAcquireRailroad

pred sellRailroad[p, p': Player, r: Railroad] {
	#p.ownedRailroads.railroads > 0
	p'.ownedRailroads.railroads = p.ownedRailroads.railroads - r
}
// If a railroad is sold, check that the relation is updated
assert checkSellingRailroad {
	all p, p': Player, r: Railroad | r in p.ownedRailroads.railroads implies sellRailroad[p, p', r] => !(r in p'.ownedRailroads.railroads)
}
//------
//------
pred acquireUtility[p, p': Player, u: Utilities] {
	p'.ownedUtilities.utilities = p.ownedUtilities.utilities ++ u
}
// If a property is bought, check that the relation is updated
assert checkAcquireUtility {
	all p, p': Player, u: Utilities | !(u in p.ownedUtilities.utilities) implies acquireUtility[p, p', u] => u in p'.ownedUtilities.utilities
}
//check checkAcquireRailroad

pred sellUtility[p, p': Player, u: Utilities] {
	#p.ownedUtilities > 0
	p'.ownedUtilities.utilities = p.ownedUtilities.utilities - u
}
// If a utility is sold, check that the relation is updated
assert checkSellingUtility {
	all p, p': Player, u: Utilities | u in p.ownedUtilities.utilities implies sellUtility[p, p', u] => !(u in p'.ownedUtilities.utilities)
}
//check checkSellingUtility for 1 but 2 Utilities
//------
//------
pred acquireHouse[p, p': Player, pr: Property, h: House] {
	#p.ownedProperties.houses < 4
	p'.ownedProperties.houses = p.ownedProperties.houses ++ pr->h
}
// If a house is bought, check that the relation is updated
assert checkAcquireHouse {
	all p, p': Player, pr: Property, h: House | acquireHouse[p, p', pr, h] => one p'.ownedProperties.houses[pr]
}
//check checkAcquireHouse

pred sellHouse[p, p': Player, pr: Property, h: House] {
	#p.ownedProperties.houses > 0
	p'.ownedProperties.houses = p.ownedProperties.houses - pr->h
}
// If a house is sold, check that the relation is updated
assert checkSellHouse {
	all p, p': Player, pr: Property, h: House | sellHouse[p, p', pr, h] => no p'.ownedProperties.houses[pr]
}
//check checkSellHouse
//------
//------
pred acquireHotel [p, p': Player, pr: Property, h: Hotel] {
	#p.ownedProperties.houses = 4
	p'.ownedProperties.hotels = p.ownedProperties.hotels ++ pr->h
}
// If a Hotel is bought, check that the relation is updated
assert checkAcquireHotel {
	all p, p': Player, pr: Property, h: Hotel | acquireHotel[p, p', pr, h] => one p'.ownedProperties.hotels[pr]
}
//check checkAcquireHotel

pred sellHotel[p, p': Player, pr: Property, h: Hotel] {
	#p.ownedProperties.hotels > 0
	p'.ownedProperties.hotels = p.ownedProperties.hotels - pr->h
}
// If a house is sold, check that the relation is updated
assert checkSellHotel {
	all p, p': Player, pr: Property, h: Hotel | sellHotel[p, p', pr, h] => no p'.ownedProperties.hotels[pr]
}
//check checkSellHotel
// ----------------------- DYNAMIC ----------------------- //

pred show (b: Board, o: OwnedProperties){
	#b.players > 1
	#o.properties > 1
	
}
run show
