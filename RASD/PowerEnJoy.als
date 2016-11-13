open util/boolean

sig Username {}

sig Address {
longitude: Int, //should be double
latitude: Int //should be double
} {
longitude > 0
latitude > 0
}

fact differentAddresses {
all a1, a2: Address | (a1 != a2) <=> (a1.latitude  != a2.latitude) || (a1.longitude != a2.longitude)
}

sig Time {
hour: Int,
minute: Int
} {
hour >= 0
minute >= 0
}

abstract sig Discount{
totalDiscount: Int
}
{
totalDiscount > 0
}

one sig Discount1 extends Discount{}

one sig Discount2 extends Discount{}

one sig Discount3 extends Discount{}

fact CarsAndReservations {
#(Reservation) = #(Car.reserved)
}

sig Reservation {
reservedCar: one Car,
user: one RegisteredUser
}

fact uniqueCarReservation{
no disj r1,r2: Reservation | (r1.reservedCar = r2.reservedCar)
}

fact uniqueUserReservation{
no disj r1,r2: Reservation | (r1.user = r2.user)
}

fact carNotReserved{
all  c: Car | no r1: Reservation | c.reserved = False && r1.reservedCar = c 
}

fact pluggedCarsInSafeArea2 {
all sa: SafeArea, c: sa.cars.elems | c.plugged = True <=> sa.specialArea = True
}

sig SafeArea {
specialArea: one Bool,
cars: seq Car
}

fact noDuplicatesInSafeArea {
all sa: SafeArea | not sa.cars.hasDups
}

fact differentCarSafeArea{
all c:Car | no disj sa1,sa2: SafeArea | (c in sa1.cars.elems && c in sa2.cars.elems)
}

sig Car {
plate: Int,
location: one Address,
reserved: one Bool, 
broken: one Bool,
ignited: one Bool,
weightSensors: Int, 
plugged: one Bool,
screen: one Screen,
lowBattery: one Bool
} {
plate>0
weightSensors > 0
weightSensors <= 5
}

fact allScreensAreOwned{
Car.screen =Screen
}

fact uniqueCar{
no disj c1,c2:Car | (c1.plate = c2.plate)
}

fact carAddress {
no disj c1,c2 : Car | (c1.location = c2.location)
}

fact carScreen {
no disj c1,c2 : Car | (c1.screen = c2.screen)
}

fact carBroken {
all c: Car | (c.broken = True) => (c.reserved = False)
}

fact carIgnited {
all c: Car | (c.ignited = True) => (c.reserved = True &&  c.broken = False)
}

fact carPlugged{
all c: Car | (c.plugged = True) => (c.ignited = False)
}

fact carLowBattery {
all c: Car | (c.lowBattery = True) => (c.reserved  =False)
}

sig Screen {
time: one Time,
discount: Discount
}

fact discountPassengers {
all c:Car, s: Screen |  (c.weightSensors >= 3) => s.discount = Discount1 
}

fact discountBattery {
all c:Car, s: Screen |  (c.lowBattery = False) => s.discount = Discount2 
}

sig RegisteredUser{
cardNumber: Int,
username: one Username
} {
cardNumber > 0
}

fact allUsernamesAreOwned{
RegisteredUser.username=Username
}
fact uniqueUsername {
no disj u1, u2: RegisteredUser | (u1.username =u2.username)
}

fact uniqueCardNumber{
no disj u1, u2: RegisteredUser | (u1.cardNumber = u2.cardNumber)
}

assert reservationAndRegisteredUser{
all r:Reservation |r.user in RegisteredUser
}
check reservationAndRegisteredUser

assert numberCarReservedAndReservation{
all c:Car, r: Reservation | c.reserved = False => c!=r.reservedCar
}
check numberCarReservedAndReservation

assert notSpecialSafeAreaDoesNotHavePluggedCar {
all sa: SafeArea, c: Car | sa.specialArea = False && c.plugged = True => c not in sa.cars.elems
}
check notSpecialSafeAreaDoesNotHavePluggedCar

pred show(){
#SafeArea=4
#Car=5
}
run show for 6
