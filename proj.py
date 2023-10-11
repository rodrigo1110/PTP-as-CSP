import sys
import json
from minizinc import Instance, Model, Solver
from datetime import time 

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





def convert_str_to_time(timestr):
    time_elements = timestr.split('h')
    return time(int(time_elements[0]), int(time_elements[1])) 

def convert_str_to_mins(timestr):
    time_elements = timestr.split('h')
    return (int(time_elements[0])*60) + int(time_elements[1]) 



def initialize_locations(input_data, ptpInstance):
    loc_ids, loc_categories = [], []
    for location in input_data['places']:
        loc_ids.append(location['id'])
        loc_categories.append(location['category'])
        #new_location = Location(location['id'], location['category'])
        #locations.append(new_location)
        #print(new_location.locID, new_location.category)
    ptpInstance['location_id'] = loc_ids
    ptpInstance['location_category'] = loc_categories

def initialize_vehicles(input_data, ptpInstance):
    veh_ids, veh_canTakes, veh_starts, veh_ends, veh_capacities, veh_availabilities_start, veh_availabilities_end = [], [], [], [], [], [], []
    canTakeMax, availabilitiesMax = 0, 0
    for vehicle in input_data['vehicles']:
        veh_ids.append(vehicle['id'])
        if(canTakeMax < len(vehicle['canTake'])):
            canTakeMax = len(vehicle['canTake'])
        veh_canTakes.append(vehicle['canTake']) #might need to add -1s for all sublists to have same size
        veh_starts.append((vehicle['start']))
        veh_ends.append((vehicle['end']))
        veh_capacities.append(vehicle['capacity'])
        if(availabilitiesMax < len(vehicle['availability'])):
            availabilitiesMax = len(vehicle['availability'])
        for availability_interval in vehicle['availability']:
            interval_elements = availability_interval.split(':')
            veh_availabilities_start.append(convert_str_to_mins(interval_elements[0]))
            veh_availabilities_end.append(convert_str_to_mins(interval_elements[1]))
    
    ptpInstance['vehicle_id'] = veh_ids
    ptpInstance['num_canTake'] = canTakeMax
    ptpInstance['vehicle_canTake'] = veh_canTakes
    ptpInstance['vehicle_start_location'] = veh_starts
    ptpInstance['vehicle_end_location'] = veh_ends
    ptpInstance['vehicle_capacity'] = veh_capacities
    ptpInstance['num_availability'] = availabilitiesMax
    ptpInstance['vehicle_availability_start'] = veh_availabilities_start
    ptpInstance['vehicle_availability_end'] = veh_availabilities_end

    #for availability_interval in vehicle['availability']:
        #    interval_elements = availability_interval.split(':')
        #    availabilities.append([convert_str_to_time(interval_elements[0]), convert_str_to_time(interval_elements[1])])
        #new_vehicle = Vehicle(vehicle['id'],vehicle['canTake'], vehicle['start'], vehicle['end'], vehicle['capacity'], availabilities)
        #vehicles.append(new_vehicle)
        #availabilities = []
        #print(new_vehicle.vehID, new_vehicle.canTake, new_vehicle.availability)

def initialize_patients(input_data, ptpInstance):
    pat_ids, pat_categories, pat_loads, pat_starts, pat_destinations, pat_ends, pat_rdvTimes, pat_rdvDurations, pat_srvDurations = [], [], [], [], [], [], [], [], []
    for patient in input_data['patients']:
        pat_ids.append(patient['id'])
        pat_categories.append(patient['category'])
        pat_loads.append(patient['load'])
        pat_starts.append(patient['start'])
        pat_destinations.append(patient['destination'])
        pat_ends.append(patient['end'])
        pat_rdvTimes.append(convert_str_to_mins(patient['rdvTime']))
        pat_rdvDurations.append(convert_str_to_mins(patient['rdvDuration']))
        pat_srvDurations.append(convert_str_to_mins(patient['srvDuration']))

    ptpInstance['patient_id'] = pat_ids
    ptpInstance['patient_category'] = pat_categories
    ptpInstance['patient_load'] = pat_loads
    ptpInstance['patient_start_location'] = pat_starts
    ptpInstance['patient_destination'] = pat_destinations
    ptpInstance['patient_end_location'] = pat_ends
    ptpInstance['rdvTime'] = pat_rdvTimes
    ptpInstance['rdvDuration'] = pat_rdvDurations
    ptpInstance['srvDuration'] = pat_srvDurations


    #for patient in input_data['patients']:
    #    rdvTime = convert_str_to_time(patient['rdvTime'])
    #    rdvDuration = convert_str_to_time(patient['rdvDuration'])
    #    srvDuration = convert_str_to_time(patient['srvDuration'])
    #    new_patient = Patient(patient['id'], patient['category'], patient['load'], patient['start'], patient['end'], patient['destination'], rdvTime, rdvDuration, srvDuration)
    #    patients.append(new_patient)
        #print(new_patient.patID, new_patient.category, new_patient.rdvDuration)



def initialize_model(input_data, ptpInstance):
    #locations, vehicles, patients, availabilities = [], [], [], []
    #sameVehicleBackward = input_data['sameVehicleBackward']
    #maxWaitTime = input_data['maxWaitTime']
    #distMatrix = input_data['distMatrix']
    ptpInstance['sameVehicleBackward'] = input_data['sameVehicleBackward']
    ptpInstance['maxWaitTime'] = convert_str_to_mins(input_data['maxWaitTime'])

    ptpInstance['num_locations'] = len(input_data['places'])
    ptpInstance['num_vehicles'] = len(input_data['vehicles'])
    ptpInstance['num_patients'] = len(input_data['patients'])

    #print('\n'.join(['\t'.join([str(cell) for cell in row]) for row in distMatrix]))

    initialize_locations(input_data, ptpInstance)
    initialize_vehicles(input_data, ptpInstance)
    initialize_patients(input_data, ptpInstance)

    ptpInstance['distMatrix'] = input_data['distMatrix']



def main():
    if len(sys.argv) != 3:
        sys.stderr.write("There must be two arguments: python proj.py <input-file-name> <output-file-name>")
        exit()

    gecode = Solver.lookup("gecode")
    ptpModel = Model("./projModel.mzn")
    ptpInstance = Instance(gecode, ptpModel)
    
    with open(sys.argv[1], "r") as input_file:
        input_data = json.load(input_file)

    initialize_model(input_data, ptpInstance)

    
    
    result = ptpInstance.solve()
    print(result)

    #print(sameVehicleBackward, maxWaitTime)
    


if __name__ == "__main__":
    main()