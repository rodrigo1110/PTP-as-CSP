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

class Trip:
    def __init__(self, origin, destination, arrivalTime, patients):
        self.origin = origin
        self.destination = destination
        self.arrivalTime = arrivalTime
        self.patients = patients



#Two states for forward trips: vehicle wants to pick up a person (activitystart + dist[patient][destination] < activityDuration) or go to a hospital
#if it wants to pickup a person then if first trip we have origin is 
#depot destination is patient location. if not first trip then we have origin is last trips destination and destination is patients location. else, if it
#wants to go to hospital then we have origin = last destination or depot and destination = closest hospital.

#In backwards we have something but two states are vehicle wants to pick up person from hospital or return a person home. if first then origin=depot or last 
#destination and destination= patient destination. if return a person home then we have origin = depot or last destination and destination = person's end

def convert_str_to_time(timestr):
    time_elements = timestr.split('h')
    return time(int(time_elements[0]), int(time_elements[1])) 

def convert_str_to_mins(timestr):
    time_elements = timestr.split('h')
    return (int(time_elements[0])*60) + int(time_elements[1]) 
def convert_mins_to_str(mins):
    hours = mins//60
    minutes = mins%60
    return "{:02d}".format(hours) + 'h' + "{:02d}".format(minutes)



def get_next_ordered_vehicle_patient(vehiclePatients, minTime):
    nextSmallestTime, nextSmallestIndex = 0, -1
    for i in range(len(vehiclePatients)):
        if(activity_start_time[i] < nextSmallestTime and activitity_start_time[i] >= minTime):
            nextSmallestTime = activitity_start_time[i]
            nextSmallestIndex = i
    return i

def sort_vehicle_patients_chronologically(vehiclePatients, vehiclePatientsStartTimes):
    return [x for _, x in sorted(zip(vehiclePatientsStartTimes,vehiclePatients))]



def obtain_return_trips_after_wait(first_origin):
    return_trips, trip_patients = [], []
    for k in range(len(patientsWaiting)):
        if(len(return_trips) == 0):
            trip_origin = first_origin
        else:
            trip_origin = return_trips[k-1].destination
        i = patientsWaiting[k]
        trip_destination = activity_ends[i]
        trip_arrivalTime = convert_mins_to_str(activity_end_time[i] + srvDurations[i]) #Or just activity_end_time[i]? Same issue as line before last.
        for j in range(k,len(patientsWaiting)):
            trip_patients.append(patientIDs[patientsWaiting[j]]) 
        return_trips.append(Trip(trip_origin,trip_destination,trip_arrivalTime,trip_patients))
        trip_patients = []
   
    return return_trips
    






def result_to_trips(result):
    global requestsSatisfied, activity_start_time, activity_duration, activity_end_time, activity_vehicle, activity_completed
    global activity_starts, activity_ends, srvDurations, patientIDs, patientsWaiting
    
    requestsSatisfied = result['objective']
    activity_start_time = result['activity_start']
    activity_duration = result['activity_duration']
    activity_end_time = result['activity_end']
    activity_vehicle = result['activity_vehicle']
    activity_completed  = result['activity_completed']

    activity_starts = pat_starts + pat_destinations
    activity_ends = pat_destinations + pat_ends
    srvDurations = pat_srvDurations + pat_srvDurations
    patientIDs = pat_ids + pat_ids
    patientsWaiting = []

    countWaiting = 0

    trip_origin, trip_destination, trip_arrivalTime = -1,-1,-1
    trip_patients = []
    trips = []

    for i in range(num_vehicles):
        trips.append([])
        vehicle = veh_ids[i]
        vehiclePatients, vehiclePatientsStartTimes = [], []
        for j in range(num_activities): #Get valid patients picked-up by vehicle
            if activity_vehicle[j] == vehicle and activity_completed[j] and activity_starts[j] != -1 and activity_ends[j] != -1: 
                vehiclePatients.append(j)
                vehiclePatientsStartTimes.append(activity_start_time[j])

        if len(vehiclePatients) == 0:
            #print("This vehicle (" , vehicle, ") doesn't transport any patient")
            continue
        
        vehiclesPatientsSorted = sort_vehicle_patients_chronologically(vehiclePatients,vehiclePatientsStartTimes)
        #print(vehiclesPatientsSorted)
        
        #first trip from depot to first patient
        trip_origin = veh_starts[i]
        trip_destination = activity_starts[vehiclesPatientsSorted[0]]
        trip_arrivalTime = convert_mins_to_str(activity_start_time[vehiclesPatientsSorted[0]])
        trip_patients = []
        trips[i].append(Trip(trip_origin,trip_destination,trip_arrivalTime,trip_patients))
       
        for k in range(len(vehiclesPatientsSorted)): #Generate trips associated to vehicle in chronological order
            n = vehiclesPatientsSorted[k] #Current patient index
            n_before = 0
            if k != len(vehiclesPatientsSorted) - 1: 
                n_after = vehiclesPatientsSorted[k+1] #Following patient index
            if k != 0:
                n_before = vehiclesPatientsSorted[k-1]
            trip_origin = trips[i][-1].destination 

            #Heading to hospital/patient's home                                                                    #only add srvDurations in arrivalTime because it ruins case when vehicle is on last patient and others
            if activity_end_time[n] - activity_start_time[n] == distMatrix[activity_starts[n]][activity_ends[n]]: #+ srvDurations[n]: #Careful: srv not reflected in activity endtimes of minizinc yet (if not meant to then remove srvDurations[i] and only add it in arrival)
                trip_destination = activity_ends[n]
                trip_arrivalTime = convert_mins_to_str(activity_end_time[n] + srvDurations[n]) #Or just activity_end_time[i]? Same issue as line before last.
                if len(trips[i][-1].patients) == 0: #Transport first patient
                    trip_patients = [patientIDs[n]]
                else:
                    if(patientIDs[n] in trips[i][-1].patients):
                        trip_patients = trips[i][-1].patients
                    else:
                        trip_patients = trips[i][-1].patients + [patientIDs[n]]
                    if(n_before > num_patients and trip_origin == activity_ends[n_before]):
                        trip_patients.remove(patientIDs[n_before])

                trips[i].append(Trip(trip_origin,trip_destination,trip_arrivalTime,trip_patients))
                #print("if", n)   
            #Picking up a patient at different location
            elif (k != len(vehiclesPatientsSorted) - 1 and 
            activity_start_time[n_after] == activity_start_time[n] + distMatrix[trip_origin][activity_starts[n_after]] + srvDurations[n] 
            and trip_origin != activity_starts[n_after]):

                trip_destination = activity_starts[n_after]
                trip_arrivalTime = convert_mins_to_str(activity_start_time[n_after])
                if len(trips[i][-1].patients) == 0: #Transport first patient
                    trip_patients = [patientIDs[n]] 
                else:
                    if(patientIDs[n] in trips[i][-1].patients):
                        trip_patients = trips[i][-1].patients
                    else:
                        trip_patients = trips[i][-1].patients + [patientIDs[n]] 
                    if(n_before > num_patients and trip_origin == activity_ends[n_before]):
                        trip_patients.remove(patientIDs[n_before])
                    
                trips[i].append(Trip(trip_origin,trip_destination,trip_arrivalTime,trip_patients))
                #print("elif", n)

            #Still need to add check for situation when patient dropped at hospital and vehicle continues (tricky - can be more than one unlike house dropoff)

            #Wait at hospital
            else:
                #print("Here", n)
                if len(patientsWaiting) != 0:
                    first = patientsWaiting[0]              #if not last patient to wait for                                                                                            #Should be just srv of n
                if len(patientsWaiting) == 0 or activity_end_time[first] - activity_start_time[n] != distMatrix[trip_origin][activity_ends[first]] + srvDurations[first] + srvDurations[n]:
                    countWaiting = countWaiting + 1
                    patientsWaiting.append(n)
                else:
                #    print("Here2")
                    patientsWaiting.append(n)
                    return_trips = obtain_return_trips_after_wait(trip_origin)
                    patientsWaiting = []
                    trips[i] = trips[i] + return_trips


            '''
            else: #Heading to pickup next patient 
                #Need way to find out what is the next patient it picks up (probably just cycle through activity start array for a possible match)
                if(k == len(vehiclesPatientsSorted)-1):
                    print("Wasn't supposed to enter here (should be last patient's return trip)")
                    continue
                else:
                    trip_destination = activity_starts[vehiclesPatientsSorted[k+1]]
                    trip_arrivalTime = convert_mins_to_str(activity_start_time[vehiclesPatientsSorted[k+1]])
                    if len(trips[i][-1].patients) == 0: #Transport first patient
                        trip_patients = [patientIDs[vehiclesPatientsSorted[k]]] #WRONG - gotta add patient we're going to pickup in trips[i][k+1].patients
                    #elif loc_categories[trip_origin] == 0: #coming from a hospital to pickup patient
                    #    trip_patients = trips[i][-1].patients
                    #    for patient in trips[i][-1].patients:
                    #        if activity_end_time[patient] < activity_end_time[n]
                    else:
                        if(patientIDs[n] in trips[i][-1].patients):
                            trip_patients = trips[i][-1].patients
                        else:
                            trip_patients = trips[i][-1].patients + [patientIDs[n]] #WRONG - gotta add patient we're going to pickup in trips[i][k+1].patients
                trips[i].append(Trip(trip_origin,trip_destination,trip_arrivalTime,trip_patients))        
            '''      
            #TODO: add cases where vehicle reaches hospital and drops patients (patient list = [] if it doesnt stand there just waiting for them)   
            #TODO: add trip where vehicle returns to depot after first availability period and starts from depot at beginning of second one
            '''
                for j in range(num_activities):
                    if activity_vehicle[j] == activity_vehicle[i]:
                        if activity_start_time[j] == activity_start_time[i] + distMatrix[trip_origin][activity_starts[j]] + srvDurations[j]:
                            trip_destination = activity_starts[j]
                            trip_arrivalTime = activity_start_time[j]
                            trip_patients.append(patientIDs[j])
                            break
                if(veh_availabilities_end[1] - distMatrix[trip_origin][veh_ends[vehicle_id]]): #Last heading to return depot
                    trip_destination = veh_ends[vehicle_index]
                    trip_arrivalTime = trips[i][k-1].arrivalTime + distMatrix[trip_origin][veh_ends[vehicle_index]]
                    trip_patients = []'''
        #Trip to return to depot
        trip_origin = trips[i][-1].destination
        trip_destination = veh_ends[i]
        trip_arrivalTime = convert_mins_to_str(convert_str_to_mins(trips[i][-1].arrivalTime) + distMatrix[trip_origin][veh_ends[i]] + srvDurations[n])
        trip_patients = []
        trips[i].append(Trip(trip_origin,trip_destination,trip_arrivalTime,trip_patients)) 
        #for trip in trips[i]:
        #   print(trip.origin, trip.destination, trip.arrivalTime, trip.patients)

    return trips
        



def trips_to_output(outputFile, trips, requestsSatisfied):
    
    output_dict = {"requests": requestsSatisfied}
    vehicles_list, trip_list = [], []
    for i in range(len(trips)):
        vehicle_dict = {}
        vehicle_dict = {'id': veh_ids[i]} 
        for trip in trips[i]:
            trip_dict = {}
            trip_dict["origin"] = trip.origin
            trip_dict["destination"] = trip.destination
            trip_dict["arrival"] = trip.arrivalTime
            trip_dict["patients"] = trip.patients
            trip_list.append(trip_dict)
        vehicle_dict["trips"] = trip_list
        vehicles_list.append(vehicle_dict)
        trip_list = []

    output_dict['vehicles'] = vehicles_list

    json_object = json.dumps(output_dict, indent = 1)
    with open(outputFile, 'w') as file:
        file.write(json_object)
    
    




def initialize_locations(input_data, ptpInstance):
    global loc_ids, loc_categories # = [], []
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
    global veh_ids, veh_canTakes, veh_starts, veh_ends, veh_capacities, veh_availabilities_start, veh_availabilities_end, first_vehicle_id
    veh_ids, veh_canTakes, veh_starts, veh_ends, veh_capacities, veh_availabilities_start, veh_availabilities_end = [], [], [], [], [], [], []
    canTakeMax, availabilitiesMax, i, first_vehicle = 0, 0, 0, 0
    for vehicle in input_data['vehicles']:
        if(i==0):
            first_vehicle_id = vehicle['id']
        veh_availabilities_start.append([])
        veh_availabilities_end.append([])
        veh_ids.append(vehicle['id'])
        #if(canTakeMax < len(vehicle['canTake'])): (cheat - assume max n of categories is 3)
        #    canTakeMax = len(vehicle['canTake']) 
        veh_canTakes.append(vehicle['canTake']) #might need to add -1s for all sublists to have same size
        veh_starts.append((vehicle['start']))
        veh_ends.append((vehicle['end']))
        veh_capacities.append(vehicle['capacity'])
        #if(availabilitiesMax < len(vehicle['availability'])): (cheat - assume max availability intervals = 2)
        #    availabilitiesMax = len(vehicle['availability'])
        for availability_interval in vehicle['availability']:
            interval_elements = availability_interval.split(':')
            veh_availabilities_start[i].append(convert_str_to_mins(interval_elements[0]))
            veh_availabilities_end[i].append(convert_str_to_mins(interval_elements[1]))
        i = i + 1
    for j in range(len(veh_canTakes)):
        while len(veh_canTakes[j]) != 3: #canTakeMax:
            veh_canTakes[j].append(-1)
            
    for k in range(len(veh_availabilities_start)):
        while len(veh_availabilities_start[k]) != 2: #availabilitiesMax:
            veh_availabilities_start[k].append(-1)
            veh_availabilities_end[k].append(-1)

    ptpInstance['vehicle_id'] = veh_ids
    ptpInstance['num_canTake'] = 3 #canTakeMax
    ptpInstance['vehicle_canTake'] = veh_canTakes
    ptpInstance['vehicle_start_location'] = veh_starts
    ptpInstance['vehicle_end_location'] = veh_ends
    ptpInstance['vehicle_capacity'] = veh_capacities
    ptpInstance['num_availability'] = 2 #availabilitiesMax
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
    global pat_ids, pat_categories, pat_loads, pat_starts, pat_destinations, pat_ends, pat_rdvTimes, pat_rdvDurations, pat_srvDurations
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
    global sameVehicleBackward, maxWaitTime, num_locations, num_vehicles, num_patients, num_activities, distMatrix

    sameVehicleBackward = input_data['sameVehicleBackward']
    maxWaitTime = convert_str_to_mins(input_data['maxWaitTime'])
    num_locations = len(input_data['places'])
    num_vehicles = len(input_data['vehicles'])
    num_patients = len(input_data['patients'])
    num_activities = num_patients * 2
    distMatrix = input_data['distMatrix']

    ptpInstance['sameVehicleBackward'] = sameVehicleBackward
    ptpInstance['maxWaitTime'] = maxWaitTime
    ptpInstance['num_locations'] = num_locations
    ptpInstance['num_vehicles'] = num_vehicles
    ptpInstance['num_patients'] = num_patients

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
    if(len(result) == 0):
        with open(sys.argv[2], 'w') as file:
            json.dump(["No solution found"], file)
        exit()
    #print(result)
    
    trips = result_to_trips(result)
    trips_to_output(sys.argv[2],trips,result['objective'])

    '''
    print(result['activity_start'][0:30])
    print(result['activity_start'][30:60])
    print(result['activity_start'][60:90])
    print(result['activity_start'][90:111])
    print(result['activity_start'][111:])
    print("-------------------------------------------------------------------------")
    print(result['activity_end'][0:30])
    print(result['activity_end'][30:60])
    print(result['activity_end'][60:90])
    print(result['activity_end'][90:111])
    print(result['activity_end'][111:])
    print("-------------------------------------------------------------------------")
    print(result['activity_vehicle'][0:30])
    print(result['activity_vehicle'][30:60])
    print(result['activity_vehicle'][60:90])
    print(result['activity_vehicle'][90:111])
    print(result['activity_vehicle'][111:])
    print("-------------------------------------------------------------------------")
    print(result['activity_completed'][0:30])
    print(result['activity_completed'][30:60])
    print(result['activity_completed'][60:90])
    print(result['activity_completed'][90:111])
    print(result['activity_completed'][111:])'''



    #print(sameVehicleBackward, maxWaitTime)
    


if __name__ == "__main__":
    main()