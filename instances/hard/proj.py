import sys

class Location:
    def __init__(self, locID, category):
        self.locID = locID
        self.category = category

class Vehicle:
    def __init__(self, vehID, canTake, startLocation, endLocation, capacity, availability):
        self.vehID = vehID
        self.canTake = canTake
        self.startLocation = startLocation
        self.endLocation = endLocation
        self.capacity = capacity
        self.availability = availability

class Patient:
    def __init__(self, patID, category, load, startLocation, endLocation, destination, rdvTime, rdvDuration, srvDuration):
        self.patID = patID
        self.category = category
        self.load = load
        self.startLocation = startLocation
        self.endLocation = endLocation
        self.destination = destination
        self.rdvTime = rdvTime
        self.rdvDuration = rdvDuration
        self.srvDuration = srvDuration

distMatrix = [[]]
maxWaitTime = 0
sameVehicleBackWard = False