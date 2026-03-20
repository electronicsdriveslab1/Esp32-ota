#include "Adafruit_FONA.h"
#include <TimeLib.h>      // Add Time library
//#include <TimeAlarms.h>   // Add TimeAlarms library
#include <HardwareSerial.h>
#include <SPIMemory.h>
#include <Arduino.h>
//#include <stdint.h>
#include <SPI.h> // Include if SPI communication is used
#include "BluetoothSerial.h"
#include <String.h>//for simcard settings and configuration
#include <Wire.h>
#include <LiquidCrystal_I2C.h>
#include <PubSubClient.h>
#include <WiFi.h>
#include <ArduinoJson.h>
#include <math.h>
//#include "nvs_flash.h"
#include <esp_system.h>
#include <WiFiClientSecure.h>
#include <HTTPClient.h>
#include <HTTPUpdate.h>
#include "time.h"


int timermissedvarload = 0;
int gpstimer = 0;
int smstimer = 0;


#define LAST_POWER_SAVE_ADDR  0x020000 //current time saving address
unsigned long lastMinuteSave = 0; //before power off time saved
bool powerCutCheckDone = false; //boolien variable to store one time run in a loop
bool BpowerCutCheckDone = false;//boolien variable to store one time run in a loop
bool CpowerCutCheckDone = false;//boolien variable to store one time run in a loop

//unsigned long lastPublish = 0;      // store last publish time MQTT
//const unsigned long Sendingdatatimeintervalofmqtt = 10000; // 10 seconds (in ms) MQTT

#define BWS_ADDRESS  0x014000   // choose any safe address (non-overlapping)
String BWS = "BLUETOOTH";
int separatesms = 1;
int linkswitches = 0;
String SWITCHSMS;
char fonaMsgBuffer[256];
char statusMessageBuffer[256];
int previousswitch = 0;

// ---- Declare globally (at the top of your code, outside any function) ----
bool pump1WasRunning = false;
bool BpumpWasRunning = false;
bool CpumpWasRunning = false;

int switchcontrolvar = 0; //SWITCH
unsigned long switchPressStartTime = 0; //SWITCH
const uint32_t SWITCHCONTROLVAR_ADDRESS = 0x00B000; // Pick a safe, unused flash memory address //SWITCH

////////////////////////TIMER///////////////////////////////
// Define addresses for storing pump schedules in SPI flash
#define PUMP1_DATA_ADDR 0X000000//0x20000 //TIMER
#define PUMP1_REMAINING_TIME_ADDRESS 0X001000//0x28000 //TIMER
// Pump variables
int pump1DurationMinutes = 0; // Duration in minutes for Pump1 //TIMER
int pump1StartHour = -1, pump1StartMinute = -1; // Start time for Pump1 //TIMER
bool pump1Running = false; // Track pump states //TIMER
unsigned long pump1RemainingTime = 0;  // Store remaining time for Pump 1 //TIMER
unsigned long pump1Counter = 0; // Countdown for Pump1 in minutes //TIMER
unsigned long lastCountdownTime = 0; // Last time the countdown was updated //TIMER
const unsigned long COUNTDOWN_INTERVAL = 60000; // 1 minute in milliseconds //TIMER
unsigned long savedRemainingPump1_global = 0;
bool pump1PostBootPending = false;

///////////////2ND TIMER////////////

#define BPUMP1_DATA_ADDR 0X00C000//0x20000 //TIMER
#define BPUMP1_REMAINING_TIME_ADDRESS 0X00D000//0x28000 //TIMER
// Pump variables
int Bpump1DurationMinutes = 0; // Duration in minutes for Pump1 //TIMER
int Bpump1StartHour = -1, Bpump1StartMinute = -1; // Start time for Pump1 //TIMER
bool Bpump1Running = false; // Track pump states //TIMER
unsigned long Bpump1RemainingTime = 0;  // Store remaining time for Pump 1 //TIMER
unsigned long Bpump1Counter = 0; // Countdown for Pump1 in minutes //TIMER
unsigned long BlastCountdownTime = 0; // Last time the countdown was updated //TIMER
const unsigned long BCOUNTDOWN_INTERVAL = 60000; // 1 minute in milliseconds //TIMER
unsigned long savedRemainingBPump_global = 0;
bool BpumpPostBootPending = false;

/////////////////3RD TIMER////////////////////

#define CPUMP1_DATA_ADDR 0X00E000//0x20000 //TIMER
#define CPUMP1_REMAINING_TIME_ADDRESS 0X00F000//0x28000 //TIMER
// Pump variables
int Cpump1DurationMinutes = 0; // Duration in minutes for Pump1 //TIMER
int Cpump1StartHour = -1, Cpump1StartMinute = -1; // Start time for Pump1 //TIMER
bool Cpump1Running = false; // Track pump states //TIMER
unsigned long Cpump1RemainingTime = 0;  // Store remaining time for Pump 1 //TIMER
unsigned long Cpump1Counter = 0; // Countdown for Pump1 in minutes //TIMER
unsigned long ClastCountdownTime = 0; // Last time the countdown was updated //TIMER
const unsigned long CCOUNTDOWN_INTERVAL = 60000; // 1 minute in milliseconds //TIMER
unsigned long savedRemainingCPump_global = 0;
bool CpumpPostBootPending = false;


///////////////////////////////////////////////////////////////////////////

const uint32_t FAILURE_COUNTER_ADDRESS = 0X002000;//0x1000; // Starting address to store failureCounter //GPS
#define LOCK_THRESHOLD 144//720  //1440 // Number of failures before locking (1DAY) (24HRS) //GPS
// Variables to track GPS failures
int failureCounter = 0; // Tracks the number of consecutive GPS failures //GPS

////LOCATION START//////////
// Variables to store the previous GPS coordinates
float previousLatitude = 0.0;//12.853558; //GPS
float previousLongitude = 0.0;//77.676506; //GPS

//#define LOCKPASSWORD_ADDRESS 0x10000 //0X19003,4 Address in flash memory for storing the password
const uint32_t LOCKPASSWORD_ADDRESS = 0X003000;//0x9000; //SYSTEM LOCK
#define LOCK_STATUS_ADDRESS 0X004000 //0x11000  //SYSTEM LOCK
String password = "1000"; // This will now be a dynamic password that can be updated //SYSTEM LOCK
String inputPassword = "0000"; // To store user input //SYSTEM LOCK
bool isLocked = false; // Track whether the system is locked //SYSTEM LOCK
int currentDigit = 0;          // Track which digit the user is inputting (0-3) //SYSTEM LOCK
bool underscoreVisible = true; // Variable to track the visibility of the underscore //SYSTEM LOCK
#define R 6371.0  // Earth radius in kilometers //SYSTEM LOCK
char callerIDbuffer[32]; //SMS
#define LOCATION_ADDRESS  0X005000 //0x19000 // Example address for storing location //GPS
float Setdistance = 0.10; //0.5 500METERS  //GPS

// Non-blocking timing variables
unsigned long gpslastCheckTime = 0; //GPS TIMER
const long gpscheckInterval = 180000; // 600000 GPS TIMER //10min //Check every 60 second  SIMCARD DETECTION AND LOCATION LOCK DETECTION
////////LOCATION END///////////
unsigned long signallastCheckTime = 0; //SIGNAL STRENGTH TIMER
const long signalcheckInterval = 601000; //SIGNAL STRENGTH TIMER   601000
////SIGNAL STRENGTH ICON//////
byte indicator0[] = {B00000,B00000,B00000,B00000,B00000,B00000,B10000,B10000}; //SIGNAL STRENGTH
byte indicator1[] = {B00000,B00000,B00000,B00000,B00100,B01100,B11100,B11100}; //SIGNAL STRENGTH
byte indicator2[] = {B00000,B00000,B00001,B00011,B00111,B01111,B11111,B11111}; //SIGNAL STRENGTH
byte Nosignal[] = {B00111,B01001,B10001,B11011,B10101,B11011,B10001,B11111};   //SIGNAL STRENGTH

////////////MQTT////////////
// MQTT broker details
const char* mqtt_server = "broker.emqx.io";  //"test.mosquitto.org"; //broker.hivemq.com  //WIFI MQTT
const int mqtt_port = 1883; //WIFI MQTT
const char* mqtt_username = ""; //your_mqtt_username //WIFI MQTT
const char* mqtt_password = ""; //your_mqtt_password //WIFI MQTT
const char* mqtt_clientId = "hical1"; //WIFI MQTT

// Define the capacity of the JSON document
const size_t capacity = JSON_OBJECT_SIZE(512); //255
// Variable to track the current mode
String currentMode = "1OFF";


WiFiClient espClient;
PubSubClient client(espClient);

unsigned long lastWifiReconnectAttempt = 0;
unsigned long lastMqttReconnectAttempt = 0;
const unsigned long wifiReconnectInterval = 60000; // Reconnect WiFi every 5 seconds//1 min
const unsigned long mqttReconnectInterval = 35000; // Reconnect MQTT every 5 seconds //35sec

//WIFI
const uint32_t SSID_ADDRESS = 0X006000;//0x3000;
const uint32_t PASSWORD_ADDRESS = 0X007000;//0x6000;
char wifi_ssid[32];
char wifi_password[32];

///SIMCOM MODEM/////
const int PWRKEY_Pin = 32;      // GPIO pin connected to the PWRKEY pin of SIM800L
const uint32_t PHONE_NUMBER_ADDRESS_1 = 0X008000;//0x12000; 
const uint32_t PHONE_NUMBER_ADDRESS_2 = 0X009000;//0x13000;

//char callerIDbuffer[32];  // Declare globally to access it in any function
char replybuffer[255];
//uint8_t readline(char *buff, uint8_t maxbuff, uint16_t timeout = 0);
String smsString = "";
bool gpsActive = true;  // Flag to control GPS execution   //NEW LINE
char fonaNotificationBuffer[64]; // for notifications from the FONA
char smsBuffer[250];
// Maximum number of allowed phone numbers to be stored
const int MAX_ALLOWED_NUMBERS = 3; //3
// Array to store the allowed phone numbers
char allowedPhoneNumbers[MAX_ALLOWED_NUMBERS][32];
int numAllowedNumbers = 0; // Start with 0 to include the initial number in the list

// Define variables to store previous states OF SMS TO USER
String previousStatusMessageSMS = "";
String currentStatusMessageSMS;

///////////////////////////////////SIM CARD NETWORK SETTINGS and configureNetworkSettings and NETWORK TIME /////////////////////////////////

struct NetworkSettings {
  const char* apn;
  const char* username;
  const char* password;
};

const NetworkSettings networkSettings[] = {
  {"airtelgprs.com", "", ""},  // Airtel // 40445 "Admin", "Adminpassword"
  {"www", "", ""},                               // Vodafone Idea (Vi) // 40486
  {"jionet", "", ""},                            // Reliance Jio //
  {"bsnlnet", "", ""},                           // BSNL
  {"TATA.DOCOMO.INTERNET", "", ""}               // Tata Docomo
  // Add more networks as needed
};

HardwareSerial SerialAT(2);
HardwareSerial *fonaSerial = &SerialAT; //HardwareSerial is often used to communicate with hardware serial ports (UART)
Adafruit_FONA_3G fona(0); // Modified constructor to set FONA_RST pin to 0

///////////////////////////////////////

LiquidCrystal_I2C lcd(0x27, 16, 2); // set the LCD address to 0x27 for a 16 chars and 2 line display
String CURRENTSTATUSDISPLAY; 
String PREVIOUSSTATUSDISPLAY;

BluetoothSerial SerialBT;
bool isConnected = false; //Bluetooth status for mqtt

bool isAutoModeSolar = false; // MOTOR sensor
const int WATER_SENSORTOP_PIN = 36; // Digital sensor pin for water presence //36
const int WATER_SENSORTOP_PIN2 = 39; // Digital sensor pin for water presence  //39
const int WATER_SENSORBOTTOM_PIN = 34; // Digital sensor pin for water presence //36
const int WATER_SENSORBOTTOM_PIN2 = 35; // Digital sensor pin for water presence  //39

int full = 0;
int pumping = 0;

const int RMS_PIN1_INPUT = 1; 
const int RMS_PIN2_INPUT = 3; 
const int RMS_PIN3_INPUT = 25;  
const int DRIVES_PIN1_OUTPUT = 26; 
const int DRIVES_PIN2_OUTPUT = 27; //DE PIN USED, NEW PCB CHANGES FOR GPIO 4

//////////switch//////////
const int switchPin1 = 33;  //33 First switch (Selection)
const int switchPin2 = 2;   //2 Second switch (Enter)
//const int switchPin3 = 4;
int selectedLogic; // = 0;        // Variable to store the selected logical condition
bool logicActivated; // = false;  // Variable to track if the logic is currently activated
int DRIVES_STATUS = 1;
////////////////////////////

const int CS_1 = 5; // Replace with your actual CS pin
//SPIFlash flash;
 SPIFlash flash(CS_1);
const uint32_t SMS_STATUS_ADDRESS = 0X00A000;//0x16000; // Adjust the address as needed

// Variable to track whether the time has been set from SMS or GSM network
bool isTimeSetFromSMS = false;


/////////MISSED SET TIME////////// 
// Define addresses in SPI flash for missed flags
#define PUMP1_MISSED_FLAG_ADDR   0x010000
#define BPUMP1_MISSED_FLAG_ADDR   0x011000
#define CPUMP1_MISSED_FLAG_ADDR   0x012000
#define LAST_RESET_DAY_ADDR 0x013000

bool pump1MissedSent = false;
bool Bpump1MissedSent = false;
bool Cpump1MissedSent = false;
int lastSavedDay = -1;

///////////////////////////////////////////////////////////////////

//LOOP SECTION
void mainloop(); //MAIN LOOP OF THE CODE FUNCTION

void updateBWSStatus(const char *newBWS); //STORES THE OPERAATED THROUGH SMS,BLUETOOTH,WIFI
String loadBWSStatus(); //RETRIVE THE OPERAATED THROUGH SMS,BLUETOOTH,WIFI

//SMS
void sms(); //USER INSTRUCTION RECEIVING LOOP OF SMS
void _2sms();
void addPhoneNumber(const char *phoneNumber); //STORE USER REGISTER PHONE NUMBER
void loadAllowedPhoneNumbers(); //RETRIVE STORED USER PHONE NUMBER
bool isPhoneNumberAllowed(const char *phoneNumber); //USER PHONE IS REGISTERED
void removePhoneNumber(const char *phoneNumber); //DELETE USER REGISTERED PHONE NUMBER
void digitalClockDisplay(); //DISPLAYING THE CURRENT TIME ON SERIAL (PUTTY) FUNCTION
void printDigits(int digits); //DISPLAYING THE CURRENT TIME ON SERIAL (PUTTY) FUNCTION
void setTimeFromGSM(); //SETTING THE TIME AND DATE FROM NETWORK
void Deletesms(); //DELETING THE STORED SMS FROM THE SIMCARD MEMORY
void configureNetworkSettings(); //GETTING THE SIMCARD OPERATOR INFORMATION
void setNetworkSettings(const NetworkSettings& settings); //GETTING THE SIMCARD OPERATOR INFORMATION
bool isSIMCardInserted(); //SIMCARD DETECTION FUNCTION
int get_network(); //GETTING THE SIGNAL STRENGTH IN PERCENTAGE (%)
void display_network(int signalStrength); //DISPLAYING THE SIGNAL BARS ON LCD
void signal(); //NETWORK SIGNAL FUNCTION

//CALL HANDELING SECTION 
//void handleIncomingCallCheck(); //ANAWERING THE INCOMING CALL
void answerIncomingCall(); //ANAWERING THE INCOMING CALL/PICKING UP THE CALL
void handleVoiceCall(); //LISTENING THE INPUT OF THE USER
char waitForDTMFTone(); //ENTERING THE NUMBERS 0-9 AND * # BY THE USER
void handleVoiceCommand(char dtmfTone); //EXECUTING THE DTMF TONE
void sendDTMFTone(char tone); //SENDING THE DTMF TONE TO SIMCOM
void hangUpCall(); // HANGUP THE CALL 


//PREVIOUS OR LAST STATE OF THE MODE'S
void updateSMSStatus(const char *newStatus); //STORE LAST STATE OF MODE'S
int loadupdatedSMSStatus(); //RETERIVE LAST STATE OF MODE'S
void Previousstate(); //LAST STATE OF MODE'S

//SWITCH SECTION STORAGE AND RETERIVING SECTION
void storeSwitchControlVar(int value); //STORE KEY ACTIVE OR DEACTIVE
int loadSwitchControlVar(); //RETERIVE KEY ACTIVE OR DEACTIVE
void DISPLAYMODES(); //DISPLAYING MODE'S SELECTION ON LCD
void performLogic(int logicNumber, bool activate); //MODE'S SELECTION THROUGH SWITCH

//WATER SENSOR FUNCTION
bool isWaterPresent(); //TOP SENSOR
bool isWaterPresent2(); //MIDDLE SENSOR

//COMMON MODE SELECTION FUNCTION
void MANUALMODEPUMP(); //COMMON MANUAL MODE PUMP ON FUNCTION
void PUMPLOADOFF(); //COMMON MANUAL MODE PUMP OFF FUNCTION
void MANUALMODEUTILITY();
void MANUALMODEPUMPUTILITY();
void AUTOMODE(); //COMMON AUTO MODE PUMP ON FUNCTION
void AUTOMODEOFF(); //COMMON AUTO MODE PUMP OFF FUNCTION
void TOPTANK(); //COMMON SENSOR OPERATION FUNCTION
void TIMERMODEPUMP(); //COMMON TIMER PUMP ON FUNCTION
void TIMEROFF(); //COMMON TIMER PUMP OFF FUNCTION
void TIMERMODEOFF(); //COMMON TIMER MODE PUMP OFF FUNCTION
void STOPPUMP1();  //COMMON TIMER STOP FUNCTION FOR PUMP1
void BSTOPPUMP1();; //COMMON TIMER STOP FUNCTION FOR BPUMP
void CSTOPPUMP1();; //COMMON TIMER STOP FUNCTION FOR CPUMP
//void restarttimerpump(); //COMMON TIMER RESTART FUNCTION FOR PUMP1
//void Brestarttimerpump(); //COMMON TIMER RESTART FUNCTION FOR BPUMP
//void Crestarttimerpump(); //COMMON TIMER RESTART FUNCTION FOR CPUMP
void stoptimermode(); //COMMON STOP TIMER MODE
void commonstoptimer(); //COMMON CHANGE OVER MODE'S, STOP'S THE TIMER

//STORAGE AND RETRIVING SECTION OF WIFI
void updateSSID(const char *newSSID); //STORE WIFI USER ID UPDATED FUNCTION
void updatePassword(const char *newPassword); //STORE WIFI USER PASSWORD UPDATED FUNCTION
void loadSSID();//RETRIVE WIFI USER ID UPDATED FUNCTION
void loadPassword();//RETRIVE WIFI USER PASSWORD UPDATED FUNCTION

//MQTT
void reconnect(); //RECONNECTING TO MQTT
void callback(char* topic, byte* payload, unsigned int length); //RECEIVING THE DATA OF MQTT
void publishStatusNow(); //MQTT DATA PUBLISH FROM BOARD

//GPS SECTION
void gps(); //LOCATION TRACKING FUNCTION
void checkLocationAndSendSMS(char* callerIDbuffer, float currentLatitude, float currentLongitude); //CHECKS THE LOCATION AND SEND A SMS TO USER LOCKED OR NOT
void handleSwitchInput(int switchState1, int switchState2); //PASSWORD UNLOCK SWITCH FUNCTION.
float haversine(float lat1, float lon1, float lat2, float lon2); //CALCULATION OF LOCATION DISTANCE
void storePreviousLocation(float previousLatitude, float previousLongitude); //STORE LOCATION
void loadPreviousLocation(float *previousLatitude, float *previousLongitude); //RETRIVE LOCATION
void updateFailureCounter(int failureCounter); //STORE GPS FAILURE COUNTER 
void loadFailureCounter(int &failureCounter); //RETRIVE GPS FAILURE COUNTER 
void checkAndHandleLockStatus(); //COMPARING THE FAILURE COUNT AND SET COUNTER

//SYSTEM LOCK SECTION
void storelockPasswordInFlash(const String& password); //STORE THE USER DEFINED SYSTEM LOCK PASSWORD
String loadlockPasswordFromFlash(); //RETRIVE THE USER DEFINED SYSTEM LOCK PASSWORD
void storeLockStatus(bool isLocked); //STORES THE BOOL VARIABLE OF SYSTEM LOCK PASSWORD
void loadLockStatus(bool *isLocked); //RETRIVE THE BOOL VARIABLE OF SYSTEM LOCK PASSWORD


//TIMER SECTION
void updatePumpSchedule(String command); //SETTING THE SET TIME AND DURATION FOR PUMP1 (COMMON)
void BupdatePumpSchedule(String command);//SETTING THE SET TIME AND DURATION FOR BPUMP (COMMON)
void CupdatePumpSchedule(String command);//SETTING THE SET TIME AND DURATION FOR CPUMP (COMMON)
void checkPumps(); //CHECKING THE SET TIME AND DURATION WITH CURRENT TIME FOR PUMP1 (COMMON)
void BcheckPumps(); //CHECKING THE SET TIME AND DURATION WITH CURRENT TIME FOR BPUMP (COMMON)
void CcheckPumps(); //CHECKING THE SET TIME AND DURATION WITH CURRENT TIME FOR CPUMP (COMMON)
void updateCountdown(); //UPDATE THE COUNTER EVERY 1MIN FOR PUMP1
void BupdateCountdown(); //UPDATE THE COUNTER EVERY 1MIN FOR BPUMP
void CupdateCountdown(); //UPDATE THE COUNTER EVERY 1MIN FOR CPUMP

//STORAGE AND RETERIVING SECTION TIMER
//STORE THE SET TIME AND DURATION FOR PUMP1
void storePump1Data(int startHour, int startMinute, int durationMinutes, unsigned long remainingTime);
//STORE THE SET TIME AND DURATION FOR BPUMP
void BstorePump1Data(int BstartHour, int BstartMinute, int BdurationMinutes, unsigned long BremainingTime);
//STORE THE SET TIME AND DURATION FOR CPUMP
void CstorePump1Data(int CstartHour, int CstartMinute, int CdurationMinutes, unsigned long CremainingTime);

//RETRIVE THE SET TIME AND DURATION FOR PUMP1
void retrievePump1Data(int &startHour, int &startMinute, int &durationMinutes, unsigned long &remainingTime);
//RETRIVE THE SET TIME AND DURATION FOR BPUMP
void BretrievePump1Data(int &BstartHour, int &BstartMinute, int &BdurationMinutes, unsigned long &BremainingTime);
//RETRIVE THE SET TIME AND DURATION FOR CPUMP
void CretrievePump1Data(int &CstartHour, int &CstartMinute, int &CdurationMinutes, unsigned long &CremainingTime);

//STORE THE REMAINING TIME FOR PUMP1
void saveRemainingTime1(unsigned long remainingTime, uint32_t address);
//STORE THE REMAINING TIME FOR BPUMP
void BsaveRemainingTime1(unsigned long BremainingTime, uint32_t Baddress);
//STORE THE REMAINING TIME FOR CPUMP
void CsaveRemainingTime1(unsigned long CremainingTime, uint32_t Caddress);

//RETRIVE THE REMAINING TIME FOR PUMP1
void loadRemainingTime1();
//RETRIVE THE REMAINING TIME FOR BPUMP
void BloadRemainingTime1();
//RETRIVE THE REMAINING TIME FOR CPUMP
void CloadRemainingTime1();


//TIMER SETUP, POWER CUT OFF AND COME BACK CALCULATES THE REMAINING TIME AND UPDATES THE COUNTER
void TIMERSETUP(); 
//POWER CUT OFF AND COME BACK CALCULATES THE REMAINING TIME
int calculateRemaining(int startHour, int startMinute, int durationMinutes);
void Pump1Missed(); //SENDS AN SMS TO USER, PUMP1 MISSIED TIME 
void BPump1Missed();//SENDS AN SMS TO USER, BPUMP MISSIED TIME
void CPump1Missed();//SENDS AN SMS TO USER, CPUMP MISSIED TIME
void savePump1MissedFlag(bool flag); //STORE MISSED TIME BOOL FLAG FOR PUMP1
bool loadPump1MissedFlag(); //RETRIVE'S MISSED TIME BOOL FLAG FOR PUMP1
void saveBPumpMissedFlag(bool flag); //STORE MISSED TIME BOOL FLAG FOR BPUMP
bool loadBPumpMissedFlag(); //RETRIVE'S MISSED TIME BOOL FLAG FOR BPUMP
void saveCPumpMissedFlag(bool flag); //STORE MISSED TIME BOOL FLAG FOR CPUMP
bool loadCPumpMissedFlag(); //RETRIVE'S MISSED TIME BOOL FLAG FOR CPUMP
void resetDailyFlags(); //RESET THE MISSED TIME BOOL FLAG AFTER 24 HOURS
void saveLastDay(int day); //STORE THE PRESENT DAY
int loadLastDay(); //RETRIVES THE PRESENT DAY
void saveCurrentMinuteToFlash(); //STORE THE CURRENT TIME
unsigned long loadLastSavedMinute(); //RETRIVE THE CURRENT TIME

void sendLocationToUsers();

void BT2();

// ================= VERSION =================
#define CURRENT_VERSION "1.1"
// ================= OTA URLS =================
String versionURL = "https://raw.githubusercontent.com/electronicsdriveslab1/Esp32-ota/main/version.txt";

String firmwareURL = "https://github.com/electronicsdriveslab1/Esp32-ota/releases/download/Esp32_ota_v1.0/firmware.bin";

void checkForUpdate();
void performOTA();
/*/ ================= OTA FUNCTION =================
void checkOTA()
{
  Serial.println("Checking firmware version...");

  WiFiClientSecure client;
  client.setInsecure();   // VERY IMPORTANT

  HTTPClient https;

  if (!https.begin(client, versionURL))
  {
    Serial.println("HTTPS begin failed");
    return;
  }

  int httpCode = https.GET();

  Serial.print("HTTP CODE: ");
  Serial.println(httpCode);

  if (httpCode == HTTP_CODE_OK)
  {
    String newVersion = https.getString();
    newVersion.trim();

    Serial.print("Server Version: ");
    Serial.println(newVersion);

    if (newVersion != CURRENT_VERSION)
    {
      Serial.println("New firmware found. Updating...");

      t_httpUpdate_return ret = httpUpdate.update(client, firmwareURL);

      switch (ret)
      {
        case HTTP_UPDATE_FAILED:
          Serial.printf("Update failed Error (%d): %s\n",
                        httpUpdate.getLastError(),
                        httpUpdate.getLastErrorString().c_str());
          break;

        case HTTP_UPDATE_NO_UPDATES:
          Serial.println("No Update.");
          break;

        case HTTP_UPDATE_OK:
          Serial.println("Update Success!");
          lcd.setCursor(0, 0);
          lcd.print("Update Success!");
          break;
      }
    }
    else
    {
      Serial.println("Firmware up to date");
    }
  }
  else
  {
    Serial.println("Version file not reachable");
  }

  https.end();
}*/

//void performOTA();
// ================= VERSION CHECK =================
void checkForUpdate() {
  Serial.println("\nChecking firmware version...");
  Serial.println(versionURL);

  Serial.print("Free Heap BEFORE VERSION CHECK: ");
  Serial.println(ESP.getFreeHeap());

  WiFiClientSecure client;
  client.setInsecure();

  HTTPClient http;
  http.begin(client, versionURL);

  int httpCode = http.GET();

  Serial.print("HTTP CODE: ");
  Serial.println(httpCode);

  if (httpCode == 200) {
    String payload = http.getString();
    payload.trim();

    Serial.print("Server Version: ");
    Serial.println(payload);

    if (payload != CURRENT_VERSION) {
      Serial.println(" New update available!");
      performOTA();
    } else {
      Serial.println(" Already up to date");
    }

  } else {
    Serial.print("HTTP ERROR: ");
    Serial.println(http.errorToString(httpCode));
  }

  http.end();
}

// ================= OTA UPDATE =================
void performOTA() {
  Serial.println("\nStarting OTA update...");

  Serial.print("Free Heap BEFORE OTA: ");
  Serial.println(ESP.getFreeHeap());

  delay(2000); // stabilize system

  WiFiClientSecure client;
  client.setInsecure();

  t_httpUpdate_return ret = httpUpdate.update(client, firmwareURL);

  switch (ret) {

    case HTTP_UPDATE_FAILED:
      Serial.printf(" Update Failed (%d): %s\n",
                    httpUpdate.getLastError(),
                    httpUpdate.getLastErrorString().c_str());
      break;

    case HTTP_UPDATE_NO_UPDATES:
      Serial.println("No updates available");
      break;

    case HTTP_UPDATE_OK:
      Serial.println(" Update successful! Rebooting...");
      break;
  }
}

// ================= SETUP =================

void setup()
{ 
  /*Serial.begin(9600);
   esp_err_t err = nvs_flash_erase();
    if (err == ESP_OK) {
        Serial.println("NVS erased successfully.");
    }
    err = nvs_flash_init();
    if (err == ESP_OK) {
        Serial.println("NVS initialized successfully.");
    }*/
  
  //ESP.restart();
  Serial.begin(9600);
  delay(300);

  esp_reset_reason_t reason = esp_reset_reason();
  Serial.print("Reset reason: ");
  Serial.println(reason);

  if (reason == ESP_RST_POWERON) {
    Serial.println("Power ON detected → doing one restart...");
    delay(1000);
    ESP.restart();
  }

  delay(50);
  lcd.init();         // initialize the lcd
  lcd.backlight();

  lcd.setCursor(0, 0);
  lcd.print("               ");
  //delay(500);
  lcd.setCursor(0, 0);
  lcd.print("LOADING....");

  
  //Serial.begin(9600);
  Serial.end(); //uart Disable command gpio1,gpio3 pin35,pin34

  SPI.begin();             // Initialize the SPI 
  pinMode(CS_1, OUTPUT);
  flash.begin();
  //flash.eraseChip();
  digitalWrite(CS_1, HIGH);

  delay(50);
  pinMode(DRIVES_PIN1_OUTPUT, OUTPUT);
  digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
  pinMode(DRIVES_PIN2_OUTPUT, OUTPUT);
  digitalWrite(DRIVES_PIN2_OUTPUT, LOW);
  //loadupdatedSMSStatus();
  //Previousstate();
  SerialBT.begin("Hical Communicator1"); //bluetooth name
  
  // Power on the SIMCOM modem using PWRKEY trigger
  pinMode(PWRKEY_Pin, OUTPUT);
  digitalWrite(PWRKEY_Pin, HIGH);
  delay(100);
  digitalWrite(PWRKEY_Pin, LOW);
  delay(1000);
  digitalWrite(PWRKEY_Pin, HIGH);
  delay(5000); // Wait for the modem to initialize
 
  //WATER SENSOR PINS
  pinMode(WATER_SENSORTOP_PIN, INPUT);
  pinMode(WATER_SENSORTOP_PIN2, INPUT);
  pinMode(WATER_SENSORBOTTOM_PIN, INPUT);
  pinMode(WATER_SENSORBOTTOM_PIN2, INPUT); 
  
  //STATUS RECEIVING PINS
  pinMode(RMS_PIN1_INPUT, INPUT_PULLDOWN);
  pinMode(RMS_PIN2_INPUT, INPUT_PULLDOWN);
  pinMode(RMS_PIN3_INPUT, INPUT_PULLDOWN);


 
  //Initialization OF UART OF SIMCOM AND ESP32
  Serial.println(F("FONA SMS caller ID test"));
  Serial.println(F("Initializing....(May take 3 seconds)"));
  fonaSerial->begin(115200, SERIAL_8N1, 16, 17, false);

  //bool fonaReady = false;
for (int i = 0; i < 5; i++) {
    Serial.println("Initializing FONA...");
    if (fona.begin(*fonaSerial)) {
        //fonaReady = true;
        Serial.println("FONA OK");
        break;
    }
    Serial.println("FONA failed... retrying");
    delay(1000);   // short retry delay
}

  //GPS Initialization
  fona.enableGPS(true);
  delay(2000); // Wait for GPS to initialize
  fona.enableGPRS(true);
  
  char cmd1[] = "AT+CGNSSPWR=0";
  char reply1[] = "OK\r\n";
  fona.sendCheckReply(cmd1, reply1);
  delay(50);
  
  char cmd2[] = "AT+CGNSSPWR=1";
  char reply2[] = "OK\r\n";
  fona.sendCheckReply(cmd2, reply2);
  delay(50);
  
  char cmd3[] = "AT+CGPSCOLD";
  char reply3[] = "OK\r\n";
  fona.sendCheckReply(cmd3, reply3);

  
  char cmd4[] = "AT+CCLK?";
  char reply4[] = "+CCLK: ";
  fona.sendCheckReply(cmd4, reply4);
  delay(5000);

  char cmd10[] = "AT+CCLK?";
  char reply10[] = "+CCLK: ";
  fona.sendCheckReply(cmd10, reply10);

  char cmd11[] = "AT+CCLK?";
  char reply11[] = "+CCLK: ";
  fona.sendCheckReply(cmd11, reply11);
  
  char cmd5[] = "AT+CLIP=1";
  char reply5[] = "OK";
  fona.sendCheckReply(cmd5, reply5);
 
  char cmd12[] = "AT+CNMI=2,1,0,0,0";
  char reply12[] = "OK";
  fona.sendCheckReply(cmd12, reply12);
  
  Serial.println("FONA Ready");

  loadAllowedPhoneNumbers(); //RETRIVE REGISTERIED USER PHONE NUMBER
  delay(50);

  setTimeFromGSM();             // Set the time from GSM network

  //Configure network settings based on detected SIM
  configureNetworkSettings();

  //SWITCH PINS
  pinMode(switchPin1, INPUT_PULLUP);
  pinMode(switchPin2, INPUT_PULLUP);

  //WiFi.begin(ssid, password);
  loadSSID(); //RETRIVE SSID OF WIFI
  loadPassword(); //RETRIVE PASSWORD OF WIFI
      
  WiFi.begin(wifi_ssid, wifi_password);
  Serial.print("IP address: ");
  Serial.println(WiFi.localIP());
  // Connect to WiFi
  Serial.println();
  Serial.println("Connecting to WiFi");
  

  // Set initial time for reconnect attempts
  lastWifiReconnectAttempt = millis();
  lastMqttReconnectAttempt = millis();
    
  password = loadlockPasswordFromFlash();
  
  //password =1000;
  //Serial.println(password);
   
  //Load the lock status from flash memory
  loadLockStatus(&isLocked);

  delay(100);
  //Load stored failure counter
    
  loadFailureCounter(failureCounter);
  checkAndHandleLockStatus();
  
  //Connect to MQTT broker
  client.setServer(mqtt_server, mqtt_port);
  client.setCallback(callback);
  client.setBufferSize(512);
  //client.setKeepAlive(60);

  // ----------------- Pump data retrieval + smart auto-resume -----------------
  BWS = loadBWSStatus(); // <--- LOAD from flash

  switchcontrolvar = loadSwitchControlVar(); // Restore value on startup
  
  DRIVES_STATUS = 1;
  //signal();
  lcd.setCursor(0, 0);
  lcd.print("               ");
  //delay(500);
  lcd.setCursor(0, 0);
  lcd.print("Waiting for");
  lcd.setCursor(0, 1);
  lcd.print("GPS Signal....");
   //Load the lock status from flash memory
  


   if(isLocked == true){
        //fona.sendSMS(callerIDbuffer, "Searching");
      char SEA[] = "searching.";
        for (int i = 0; i < numAllowedNumbers; i++) {
        fona.sendSMS(allowedPhoneNumbers[i], SEA);}
        }else
        {
          char SEA[] = "Searching";
        for (int i = 0; i < numAllowedNumbers; i++) {
        fona.sendSMS(allowedPhoneNumbers[i], SEA);}
        }
 Deletesms();

 ////////////////////////////////////////////////
  // WiFi Connect
  WiFi.begin(wifi_ssid, wifi_password);
  Serial.print("Connecting WiFi");

  while (WiFi.status() != WL_CONNECTED) {
    delay(500);
    Serial.print(".");
  }

  Serial.println("\nWiFi Connected");

  delay(2000);

  // ================= TIME SYNC =================
  configTime(0, 0, "pool.ntp.org");

  Serial.print("Syncing time");
  time_t now = time(nullptr);

  while (now < 100000) {
    delay(500);
    Serial.print(".");
    now = time(nullptr);
  }

  Serial.println("\nTime synced");

  // ================= HEAP CHECK =================
  Serial.print("Free Heap BEFORE HTTPS: ");
  Serial.println(ESP.getFreeHeap());

  // ================= HTTPS TEST =================
  WiFiClientSecure client;
  client.setInsecure();

  delay(2000);

  Serial.println("Connecting to Google...");

  if (client.connect("www.google.com", 443)) {
    Serial.println(" HTTPS WORKING");

    client.println("GET / HTTP/1.0");
    client.println("Host: www.google.com");
    client.println("User-Agent: ESP32");
    client.println("Connection: close");
    client.println();

  } else {
    Serial.println(" HTTPS NOT WORKING");
  }

  client.stop();

  Serial.print("Free Heap AFTER HTTPS: ");
  Serial.println(ESP.getFreeHeap());

  // ================= DNS TEST =================
  IPAddress ip;
  if (WiFi.hostByName("raw.githubusercontent.com", ip)) {
    Serial.print("DNS OK: ");
    Serial.println(ip);
  } else {
    Serial.println("DNS FAILED");
  }

  // ================= OTA CHECK =================
  if (WiFi.status() == WL_CONNECTED) {
    checkForUpdate();
  }

  lcd.setCursor(0, 0);
  lcd.print("HI");

}

void loop()
{   
  

  //Read switch states
    int switchState1 = digitalRead(switchPin1);
    int switchState2 = digitalRead(switchPin2);
    // If the system is locked, only allow location tracking
    if (isLocked) {
        BT2();

        if (!client.connected()) {
            reconnect();     // your reconnect()
    }
    else {
        client.loop();       //required
    }
       
        _2sms();
        delay(200);
        handleSwitchInput(switchState1, switchState2); //switchState3
        digitalWrite(DRIVES_PIN1_OUTPUT,LOW);
        digitalWrite(DRIVES_PIN2_OUTPUT,LOW);
    }
    else{
    unsigned long currentMillis2 = millis();  // Current time for non-blocking delays
      // Check SIM status and network every second
      if (currentMillis2 - gpslastCheckTime >= gpscheckInterval) {
        gpslastCheckTime = currentMillis2;
        if(gpstimer == 0)
        {
        gps();   
      
      }
    }
    }

///////////////////wifi connection and mqtt///////
if (!isLocked) {
unsigned long lastWiFiCheck = 0;
//Try WiFi reconnect every 5 sec
if (millis() - lastWiFiCheck >= 5000) {
    lastWiFiCheck = millis();

    if (WiFi.status() != WL_CONNECTED) {
        Serial.println("WiFi lost — reconnecting...");
        WiFi.disconnect(true);
        delay(200);
        WiFi.begin(wifi_ssid, wifi_password);   //your same variables
        
    }
}

// MQTT reconnect logic (your same variable)
if (WiFi.status() == WL_CONNECTED && WiFi.localIP().toString() != "0.0.0.0") {

    if (!client.connected()) {

            reconnect();     // your reconnect()
            
    }
    else {
        client.loop();       //required
    }
}





////////////////////////////////////////////////////////

if(smstimer == 0)
  {
    BT2();
    publishStatusNow();
    delay(2000);
    _2sms();
}
}

   if(smstimer == 1)
  {
    
    //Read switch states
    int switchState1 = digitalRead(switchPin1);
    int switchState2 = digitalRead(switchPin2);
    // If the system is locked, only allow location tracking
    if (isLocked) {
        delay(200);
        handleSwitchInput(switchState1, switchState2); //switchState3
        digitalWrite(DRIVES_PIN1_OUTPUT,LOW);
        digitalWrite(DRIVES_PIN2_OUTPUT,LOW);
    } else 
    {
      
      if(timermissedvarload == 0){
        loadupdatedSMSStatus();
         Previousstate();
        delay(1000);
      TIMERSETUP();
      
        //MISSED SET TIME///
  pump1MissedSent  = loadPump1MissedFlag();
  Bpump1MissedSent = loadBPumpMissedFlag();
  Cpump1MissedSent = loadCPumpMissedFlag();
  lastSavedDay     = loadLastDay();
      timermissedvarload = 1;}


      sms();
      mainloop(); 
    
      unsigned long currentMillis3 = millis();  // Current time for non-blocking delay
      // Check SIM status and network every second
     if (currentMillis3 - signallastCheckTime >= signalcheckInterval) {
       signallastCheckTime = currentMillis3;
       signal();  
     }
       
    }
  }
}

/*****************************************************************************************
           MAIN LOOP OF THE CODE FUNCTION
 *****************************************************************************************/
void mainloop(){
  

unsigned long lastWiFiCheck = 0;
//Try WiFi reconnect every 5 sec
if (millis() - lastWiFiCheck >= 5000) {
    lastWiFiCheck = millis();

    if (WiFi.status() != WL_CONNECTED) {
        Serial.println("WiFi lost — reconnecting...");
        WiFi.disconnect(true);
        delay(200);
        WiFi.begin(wifi_ssid, wifi_password);   //your same variables
    }
}

// MQTT reconnect logic (your same variable)
if (WiFi.status() == WL_CONNECTED && WiFi.localIP().toString() != "0.0.0.0") {

    if (!client.connected()) {

        if (millis() - lastMqttReconnectAttempt >= mqttReconnectInterval) {
            lastMqttReconnectAttempt = millis();
            reconnect();     // your reconnect()
        }
    }
    else {
        client.loop();       //required
    }
}


//#define MQTT_CONNECTED 0
//if (isConnected = false && !WiFi.isConnected() && client.state() != MQTT_CONNECTED) 
if (!isConnected && !WiFi.isConnected() && client.state() != MQTT_CONNECTED) 
{
    BWS = "SMS"; // Change mode to SMS
    updateBWSStatus(BWS.c_str());  // Store to flash
    linkswitches = 0;
}

  // Call the countdown update function every loop iteration
  updateCountdown();
  checkPumps();
  delay(50);
  BupdateCountdown();
  BcheckPumps();
  delay(50);
  CupdateCountdown();
  CcheckPumps();
  delay(50);

  Pump1Missed();
   delay(700);
  BPump1Missed();
   delay(700);
  CPump1Missed();

  ////////////////////switch/////////////////////////////////
  //Read the state of the first switch (Selection)
  int switchState1 = digitalRead(switchPin1);
    // Read the state of the second switch (Enter)
  int switchState2 = digitalRead(switchPin2);
  ////////////////////////////////////
  
  if (switchState2 == LOW) { // Button is pressed
    if (switchPressStartTime == 0) {
      switchPressStartTime = millis(); // Start timing
    }
    if (millis() - switchPressStartTime >= 10000) { // 10 seconds
      switchcontrolvar = 1;
      storeSwitchControlVar(switchcontrolvar);
      switchPressStartTime = 0; // Reset timer so it doesn't keep setting
    }
  } else {
    // Button released — reset everything
    switchPressStartTime = 0;
  }
  ////////////////////////////////////

  // If the first switch is pressed, manually select the logic
  if (switchState1 == LOW) {
    if(switchcontrolvar == 1){
    DRIVES_STATUS = 0;
    selectedLogic = (selectedLogic + 1) % 4;  // Cycle through the logical conditions
    lcd.clear();
    lcd.setCursor(0, 0);
    //lcd.print("               ");
    lcd.print("MODE:");
    delay(300); //500
    logicActivated = false;
    digitalWrite(DRIVES_PIN1_OUTPUT,LOW);
    //digitalWrite(DRIVES_PIN2_OUTPUT,HIGH);
    DISPLAYMODES();
  } 
  }

  // If the third switch is pressed, toggle the logic state
  if (switchState2 == LOW) {
    if(switchcontrolvar == 1){
    lcd.clear();
    lcd.setCursor(0, 0);
    //lcd.print("               ");
    lcd.print("MODE");
    lcd.setCursor(5, 0);
    lcd.print(logicActivated ? "OFF" : "ON");
    delay(300); //500
    logicActivated = !logicActivated;  // Toggle the logic state
    performLogic(selectedLogic, logicActivated);
    delay(100);
    DRIVES_STATUS = 1;

    if(CURRENTSTATUSDISPLAY == "PUMP ON SOLAR"){ //S+G(GRAY)+P+U(GRAY)
      lcd.setCursor(4, 1);
      lcd.print("PUMP ON");
      delay(1000);
      }else if(CURRENTSTATUSDISPLAY == "UTILITY ON SOLAR"){ //S+G(GRAY)+P(GRAY)+U
      lcd.setCursor(3, 1);
      lcd.print("UTILITY ON"); 
      delay(1000);
      }else if(CURRENTSTATUSDISPLAY == "PUMP UTILITY ON GRID"){ //S(GRAY)+G+P+U
      lcd.setCursor(0, 1);
      lcd.print("PUMP+UTILITY ON"); 
      delay(1000);
      }else if(CURRENTSTATUSDISPLAY == "UTILITY ON GRID"){ //S(GRAY)+G+P(GRAY)+U
      lcd.setCursor(3, 1);
      lcd.print("UTILITY ON"); 
      delay(1000);
      }else if(CURRENTSTATUSDISPLAY == "PUMP UTILITY ON HYBRID"){ //S+G+P+U
      lcd.setCursor(0, 1);
      lcd.print("PUMP+UTILITY ON");
      delay(1000);
      }else if(CURRENTSTATUSDISPLAY == "UTILITY ON HYBRID"){ //S+G+P(GRAY)+U
      lcd.setCursor(3, 1);
      lcd.print("UTILITY ON"); 
      delay(1000);
      }
    }
  }
///////////////SWITCH ENDS//////////////////

///////////////////READ INPUT PINS///////////////////////////
if (DRIVES_STATUS == 1) {

    int input1State = digitalRead(RMS_PIN1_INPUT);
    int input2State = digitalRead(RMS_PIN2_INPUT);
    int input3State = digitalRead(RMS_PIN3_INPUT);

    // Determine the current status based on inputs
    if (input1State == LOW && input2State == LOW && input3State == HIGH) {
      currentStatusMessageSMS = "PUMP ON SOLAR";//"S+G(GRAY)+P+U(GRAY)";
      CURRENTSTATUSDISPLAY = "PUMP ON SOLAR";//"S+G(GRAY)+P+U(GRAY)"; 
     
    } else if (input1State == HIGH && input2State == LOW && input3State == LOW) {
      currentStatusMessageSMS = "UTILITY ON SOLAR";//"S+G(GRAY)+P(GRAY)+U";
      CURRENTSTATUSDISPLAY = "UTILITY ON SOLAR";//"S+G(GRAY)+P(GRAY)+U";
  
    } else if (input1State == HIGH && input2State == HIGH && input3State == LOW) {
      currentStatusMessageSMS = "PUMP UTILITY ON GRID";//"S(GRAY)+G+P+U";
      CURRENTSTATUSDISPLAY = "PUMP UTILITY ON GRID";//"S(GRAY)+G+P+U";
    
    } else if (input1State == HIGH && input2State == LOW && input3State == HIGH) {
      currentStatusMessageSMS = "UTILITY ON GRID";//"S(GRAY)+G+P(GRAY)+U";
      CURRENTSTATUSDISPLAY = "UTILITY ON GRID";//"S(GRAY)+G+P(GRAY)+U";
      
    } else if (input1State == LOW && input2State == HIGH && input3State == LOW) {
      currentStatusMessageSMS = "PUMP UTILITY ON HYBRID";//"S+G+P+U";
      CURRENTSTATUSDISPLAY = "PUMP UTILITY ON HYBRID";//"S+G+P+U";
     
    } else if (input1State == LOW && input2State == HIGH && input3State == HIGH) {
      currentStatusMessageSMS = "UTILITY ON HYBRID";//"S+G+P(GRAY)+U";
      CURRENTSTATUSDISPLAY = "UTILITY ON HYBRID";//"S+G+P(GRAY)+U";
    
    }
    else if (input1State == HIGH && input2State == HIGH && input3State == HIGH) {
      currentStatusMessageSMS = "PUMP UTILITY OFF";//"S+G+P(GRAY)+U";
      CURRENTSTATUSDISPLAY = "PUMP UTILITY OFF";//"S+G+P(GRAY)+U";
      
    } 
    if (input1State == LOW && input2State == LOW && input3State == LOW) {
     
  currentStatusMessageSMS = "SYSTEM OFF";//"S+G+P(GRAY)+U";
      CURRENTSTATUSDISPLAY = "SYSTEM OFF";//"S+G+P(GRAY)+U";
      saveCurrentMinuteToFlash();
  }
    // Check if the status message has changed
    if (CURRENTSTATUSDISPLAY != PREVIOUSSTATUSDISPLAY) {  
      // Update LCD
      lcd.setCursor(0, 1);
      lcd.print("               "); // Clear previous message
      delay(500);
      if(CURRENTSTATUSDISPLAY == "PUMP ON SOLAR"){ //S+G(GRAY)+P+U(GRAY)
      lcd.setCursor(4, 1);
      lcd.print("PUMP ON");
      delay(500); //1000
      }else if(CURRENTSTATUSDISPLAY == "UTILITY ON SOLAR"){ //S+G(GRAY)+P(GRAY)+U
      lcd.setCursor(3, 1);
      lcd.print("UTILITY ON"); 
      delay(500);
      }else if(CURRENTSTATUSDISPLAY == "PUMP UTILITY ON GRID"){ //S(GRAY)+G+P+U
      lcd.setCursor(0, 1);
      lcd.print("PUMP+UTILITY ON"); 
      delay(500);
      }else if(CURRENTSTATUSDISPLAY == "UTILITY ON GRID"){ //S(GRAY)+G+P(GRAY)+U
      lcd.setCursor(3, 1);
      lcd.print("UTILITY ON"); 
      delay(500);
      }else if(CURRENTSTATUSDISPLAY == "PUMP UTILITY ON HYBRID"){ //S+G+P+U
      lcd.setCursor(0, 1);
      lcd.print("PUMP+UTILITY ON");
      delay(500);
      }else if(CURRENTSTATUSDISPLAY == "UTILITY ON HYBRID"){ //S+G+P(GRAY)+U
      lcd.setCursor(3, 1);
      lcd.print("UTILITY ON"); 
      delay(500);
      }else if(CURRENTSTATUSDISPLAY == "PUMP UTILITY OFF"){ //S+G+P(GRAY)+U
      lcd.setCursor(3, 1);
      lcd.print("PUMP UTILITY OFF"); 
      delay(500);
      }
      else if(CURRENTSTATUSDISPLAY == "SYSTEM OFF"){ //S+G+P(GRAY)+U
      lcd.setCursor(3, 1);
      lcd.print("SYSTEM OFF"); 
      delay(500);
      }
      // Update the previous status DISPLAY
      PREVIOUSSTATUSDISPLAY = CURRENTSTATUSDISPLAY;
    }

//WHILE OPERATING THROUGH SMS
if(BWS == "SMS"){
     if (currentStatusMessageSMS != previousStatusMessageSMS) {
      // Send SMS to all allowed numbers
      char statusMessageBuffer[255]; // Adjust size as needed
      currentStatusMessageSMS.toCharArray(statusMessageBuffer, sizeof(statusMessageBuffer));

      for (int i = 0; i < numAllowedNumbers; i++) {
        fona.sendSMS(allowedPhoneNumbers[i], statusMessageBuffer);
      }

char smsBuffer[50];
  // ----- Pump1 -----
  if (pump1Counter > 0 && !pump1WasRunning) {
    // Pump1 just started
    sprintf(smsBuffer, "Pump1 Remaining Time: %lu", pump1Counter);
    for (int i = 0; i < numAllowedNumbers; i++) {
      fona.sendSMS(allowedPhoneNumbers[i], smsBuffer);
    }
    pump1WasRunning = true;
  }
   if (pump1Counter == 0 && pump1WasRunning) {
    // Pump1 just stopped
    sprintf(smsBuffer, "Pump1 Remaining Time: %lu", pump1Counter);
    for (int i = 0; i < numAllowedNumbers; i++) {
      fona.sendSMS(allowedPhoneNumbers[i], smsBuffer);
    }
    pump1WasRunning = false;
  }

  // ----- BPump -----
  if (Bpump1Counter > 0 && !BpumpWasRunning) {
    sprintf(smsBuffer, "BPump Remaining Time: %lu", Bpump1Counter);
    for (int i = 0; i < numAllowedNumbers; i++) {
      fona.sendSMS(allowedPhoneNumbers[i], smsBuffer);
    }
    BpumpWasRunning = true;
  }
   if (Bpump1Counter == 0 && BpumpWasRunning) {
    sprintf(smsBuffer, "BPump Remaining Time: %lu", Bpump1Counter);
    for (int i = 0; i < numAllowedNumbers; i++) {
      fona.sendSMS(allowedPhoneNumbers[i], smsBuffer);
    }
    BpumpWasRunning = false;
  }

  // ----- CPump -----
  if (Cpump1Counter > 0 && !CpumpWasRunning) {
    sprintf(smsBuffer, "CPump Remaining Time: %lu", Cpump1Counter);
    for (int i = 0; i < numAllowedNumbers; i++) {
      fona.sendSMS(allowedPhoneNumbers[i], smsBuffer);
    }
    CpumpWasRunning = true;
  }
   if (Cpump1Counter == 0 && CpumpWasRunning) {
    sprintf(smsBuffer, "CPump Remaining Time: %lu", Cpump1Counter);
    for (int i = 0; i < numAllowedNumbers; i++) {
      fona.sendSMS(allowedPhoneNumbers[i], smsBuffer);
    }
    CpumpWasRunning = false;
  }
      // Update the previous status message
      previousStatusMessageSMS = currentStatusMessageSMS;

    }
  }
       delay(100);
      SerialBT.println(String(currentStatusMessageSMS) + "|" + pump1Counter + "|" + Bpump1Counter + "|" + Cpump1Counter + "|" + switchcontrolvar + "|" + linkswitches);

      publishStatusNow();
      delay(500); //2000
  }


/////////////////////////////////////////////////
// Send SMS to all allowed numbers
if(BWS == "BLUETOOTH" || BWS == "WIFI"){
if(separatesms == 1) {
      
      char statusMessageBuffer[255]; // Adjust size as needed
      currentStatusMessageSMS.toCharArray(statusMessageBuffer, sizeof(statusMessageBuffer));

      if(switchcontrolvar == 1)
      {
        char msg17[] = "keyactive";
        //fona.sendSMS(callerIDbuffer, msg17);
        for (int i = 0; i < numAllowedNumbers; i++) {
        fona.sendSMS(allowedPhoneNumbers[i], msg17);
      }
      }
      else if(switchcontrolvar == 0){
        char msg18[] = "keydeactive";
        //fona.sendSMS(callerIDbuffer, msg18);
        for (int i = 0; i < numAllowedNumbers; i++) {
        fona.sendSMS(allowedPhoneNumbers[i], msg18);
      }
      }
      delay(500); //2000

      for (int i = 0; i < numAllowedNumbers; i++) {
        fona.sendSMS(allowedPhoneNumbers[i], statusMessageBuffer);
      }
      
      char smsBuffer[50];
  // ----- Pump1 -----
  if (pump1Counter > 0 && !pump1WasRunning) {
    // Pump1 just started
    sprintf(smsBuffer, "Pump1 Remaining Time: %lu", pump1Counter);
    for (int i = 0; i < numAllowedNumbers; i++) {
      fona.sendSMS(allowedPhoneNumbers[i], smsBuffer);
    }
    pump1WasRunning = true;
  }
   if (pump1Counter == 0 && pump1WasRunning) {
    // Pump1 just stopped
    sprintf(smsBuffer, "Pump1 Remaining Time: %lu", pump1Counter);
    for (int i = 0; i < numAllowedNumbers; i++) {
      fona.sendSMS(allowedPhoneNumbers[i], smsBuffer);
    }
    pump1WasRunning = false;
  }

  // ----- BPump -----
  if (Bpump1Counter > 0 && !BpumpWasRunning) {
    sprintf(smsBuffer, "BPump Remaining Time: %lu", Bpump1Counter);
    for (int i = 0; i < numAllowedNumbers; i++) {
      fona.sendSMS(allowedPhoneNumbers[i], smsBuffer);
    }
    BpumpWasRunning = true;
  }
   if (Bpump1Counter == 0 && BpumpWasRunning) {
    sprintf(smsBuffer, "BPump Remaining Time: %lu", Bpump1Counter);
    for (int i = 0; i < numAllowedNumbers; i++) {
      fona.sendSMS(allowedPhoneNumbers[i], smsBuffer);
    }
    BpumpWasRunning = false;
  }

  // ----- CPump -----
  if (Cpump1Counter > 0 && !CpumpWasRunning) {
    sprintf(smsBuffer, "CPump Remaining Time: %lu", Cpump1Counter);
    for (int i = 0; i < numAllowedNumbers; i++) {
      fona.sendSMS(allowedPhoneNumbers[i], smsBuffer);
    }
    CpumpWasRunning = true;
  }
   if (Cpump1Counter == 0 && CpumpWasRunning) {
    sprintf(smsBuffer, "CPump Remaining Time: %lu", Cpump1Counter);
    for (int i = 0; i < numAllowedNumbers; i++) {
      fona.sendSMS(allowedPhoneNumbers[i], smsBuffer);
    }
    CpumpWasRunning = false;
  }
      
      separatesms = 0;
}
}
//////////////////////////////////BLUETOOTH LOOP START///////////////////////////////////////////////////////////

if (!isConnected && SerialBT.connected()) {
    isConnected = true;
    Serial.println("Bluetooth connected!");
    BWS = "BLUETOOTH";    // current mode you want to store
    updateBWSStatus(BWS.c_str());  // <--- STORE to flash
    linkswitches = 0;
  } else if (isConnected && !SerialBT.connected()) {
    isConnected = false;
    Serial.println("Bluetooth disconnected!");
  }

  // Check for available data
  if (SerialBT.available()) {
    String command = SerialBT.readStringUntil('\n');
    command.trim();

     BWS = "BLUETOOTH";    // current mode you want to store
    updateBWSStatus(BWS.c_str());  // <--- STORE to flash
    linkswitches = 0;
    
    // Handle single-character commands
    if (command == "MANUAL PUMP") {
      MANUALMODEPUMP();
      Serial.println("Pump started (Manual Mode).");
    } 
    else if (command == "PUMP UTILITY OFF") {
      PUMPLOADOFF();
      Serial.println("PUMP UTILITY STOPED (Manual Mode).");
    }
    else if (command == "MANUAL UTILITY") {
      MANUALMODEUTILITY();
      Serial.println("UTILITY started(Manual Mode).");
    }
    else if (command == "MANUAL PUMP UTILITY") {
      MANUALMODEPUMPUTILITY();
      Serial.println("PUMP UTILTIY started(Manual Mode).");
    }
     else if (command == "AUTO MODE") {
      AUTOMODE();
      Serial.println("Auto Mode activated.");
    }
    else if (command == "AUTO MODE OFF") {
      AUTOMODEOFF();
      Serial.println("Auto Mode OFF activated.");
    }
    
    else if (command.startsWith("E")) { // Update SSID in a single step
    String newSSID = command.substring(1); // Extract the part after "E"
    newSSID.trim(); // Remove unnecessary spaces or newline characters

    if (newSSID.length() > 0) {
        updateSSID(newSSID.c_str()); // Update SSID
        WiFi.begin(newSSID.c_str(), wifi_password); // Reconnect WiFi with updated SSID
        SerialBT.print("SSID updated successfully to: ");
        SerialBT.println(newSSID);
    } else {
        SerialBT.print("Invalid SSID. Please provide a valid one.");
    }
    loadSSID(); //RETRIVE SSID OF WIFI
  
} 
else if (command.startsWith("F")) { // Update WiFi Password in a single step
    String newPassword = command.substring(1); // Extract the part after "F"
    newPassword.trim(); // Remove unnecessary spaces or newline characters

    if (newPassword.length() > 0) {
        updatePassword(newPassword.c_str()); // Update password
        WiFi.begin(wifi_ssid, newPassword.c_str()); // Reconnect WiFi with updated password
        SerialBT.print("WiFi password updated successfully.");
    } else {
        SerialBT.print("Invalid password. Please provide a valid one.");
    }
    loadPassword(); //RETRIVE PASSWORD OF WIFI
} 

// SIMCARD AND GPS UNPLUG PASSWORD
   else if (command.startsWith("H")) { // Command to set the password via Bluetooth
    String newPassword = command.substring(1); // Extract the part after "H"
    newPassword.trim(); // Remove any unwanted spaces or newline characters

    // Check if the new password is valid (e.g., 4 digits)
    if (newPassword.length() == 4 && newPassword.toInt() != 0) {
        password = newPassword; // Update the password
        storelockPasswordInFlash(password); // Store the new password in flash memory
        SerialBT.print("Password updated successfully.");
        Serial.println("Password updated to: " + password);
    } else {
        SerialBT.print("Invalid password format. Please use a 4-digit password.");
    }
}

else if (command == "G") { // Retrieve IP and send it over Bluetooth
    DRIVES_STATUS = 0; // Disable drives temporarily
    delay(5000);

    // Get and send the local IP address
    IPAddress localIP = WiFi.localIP();
    String ipAddress = localIP.toString();
    SerialBT.print("Local IP: ");
    SerialBT.println(ipAddress);

    delay(2000);
    DRIVES_STATUS = 1; // Re-enable drives
}

else if (command.startsWith ("GET LOCATION")) {
    sendLocationToUsers();   // SMS only
    
}


    // Handle text-based commands (e.g., scheduling pumps)
    else if (command.startsWith("PUMP:")) {
      updatePumpSchedule(command); // Function to parse and schedule Pump1
      delay(200);
      pump1MissedSent = false;
      savePump1MissedFlag(false);
    }
     else if (command.startsWith("BPUMP:")) {
      BupdatePumpSchedule(command); // Function to parse and schedule Pump1
      delay(200);
      Bpump1MissedSent = false;
      saveBPumpMissedFlag(false);
    }
     else if (command.startsWith("CPUMP:")) {
      CupdatePumpSchedule(command); // Function to parse and schedule Pump1
      delay(200);
      Cpump1MissedSent = false;
      saveCPumpMissedFlag(false);
    }
     else if (command.startsWith("STOP PUMP")) {
      STOPPUMP1();
    } 
    else if (command.startsWith("STOP BPUMP")) {
      BSTOPPUMP1();
    } 
    else if (command.startsWith("STOP CPUMP")) {
      CSTOPPUMP1();
    } 
    else if (command.startsWith("STOP TIMER")) {
      stoptimermode();
    }
    else if (command == "keyactive") { 
      switchcontrolvar = 1;
      storeSwitchControlVar(switchcontrolvar);      
      }
    else if (command == "keydeactive") { 
      switchcontrolvar = 0;
      storeSwitchControlVar(switchcontrolvar);
      }
  }
 

  ////////////////////////END//////////////////////////////


//MODEL 1 UPDATE
   if(previousswitch == 1){
    linkswitches = 1;
    publishStatusNow();

    SWITCHSMS = "SWITCHMANUALPUMPON";
          SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], fonaMsgBuffer);
          }
    previousswitch = 0;
  }
  else if(previousswitch == 2)
  {
    linkswitches = 2;
    publishStatusNow();

    SWITCHSMS = "SWITCHMANUALPUMPUTILITYOFF";
          SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], fonaMsgBuffer);
          }
    previousswitch = 0;
  }
   else if(previousswitch == 3)
  {
    linkswitches = 3;
    publishStatusNow();

    SWITCHSMS = "SWITCHMANUALUTILITYON";
          SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], fonaMsgBuffer);
          }
    previousswitch = 0;
  }
   else if(previousswitch == 4)
  {
    linkswitches = 4;
    publishStatusNow();

    SWITCHSMS = "SWITCHMANUALPUMPUTILITYON";
          SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], fonaMsgBuffer);
          }
    previousswitch = 0;
  }
  else if(previousswitch == 5)
  {
    linkswitches = 5;
    publishStatusNow();

    SWITCHSMS = "SWITCHAUTOON";
          SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], fonaMsgBuffer);
          }
    previousswitch = 0;
  }
  else if(previousswitch == 6)
  {
    linkswitches = 6;
    publishStatusNow();

    SWITCHSMS = "SWITCHAUTOOFF";
          SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], fonaMsgBuffer);
          }
    previousswitch = 0;
  }

  


}

/*****************************************************************************************
           STORES THE OPERATED THROUGH SMS,BLUETOOTH,WIFI
 *****************************************************************************************/
void updateBWSStatus(const char *newBWS) {
  SPI.begin();
  uint32_t bwsAddress = BWS_ADDRESS;
  digitalWrite(CS_1, LOW); // Select the flash chip

  // Erase sector before writing
  flash.eraseSector(bwsAddress);

  // Write the string characters
  for (int i = 0; i < strlen(newBWS); i++) {
    flash.writeByte(bwsAddress + i, newBWS[i]);
  }
  // Add null-terminator
  flash.writeByte(bwsAddress + strlen(newBWS), '\0');

  digitalWrite(CS_1, HIGH); // Deselect
  Serial.println("Updated BWS Mode in Flash:");
  Serial.println(newBWS);
  SPI.endTransaction();
}

/*****************************************************************************************
           RETRIVE THE OPERAATED THROUGH SMS,BLUETOOTH,WIFI
 *****************************************************************************************/
String loadBWSStatus() {
  SPI.begin();
  char buffer[16]; // enough for "BLUETOOTH", "WIFI", or "SMS"
  uint32_t bwsAddress = BWS_ADDRESS;
  digitalWrite(CS_1, LOW);

  for (int i = 0; i < sizeof(buffer) - 1; i++) {
    buffer[i] = flash.readByte(bwsAddress + i);
    if (buffer[i] == '\0') break;
  }

  digitalWrite(CS_1, HIGH);
  buffer[sizeof(buffer) - 1] = '\0';
  SPI.end();

  Serial.print("Loaded BWS Mode from Flash: ");
  Serial.println(buffer);
  return String(buffer);
}

/*****************************************************************************************
           USER INSTRUCTION RECEIVING LOOP OF SMS
 *****************************************************************************************/
void sms(){
 
 
  char *bufPtr = fonaNotificationBuffer; // handy buffer pointer
  
  if (fona.available()) // any data available from the FONA?
  {
  
    
    int slot = 1; // this will be the slot number of the SMS
    int charCount = 0;
    // Read the notification into fonaInBuffer
    do
    {
      *bufPtr = fona.read();
      Serial.write(*bufPtr);
      delay(1);
    } while ((*bufPtr++ != '\n') && (fona.available()) && (++charCount < (sizeof(fonaNotificationBuffer) - 1)));
  
    // Add a terminal NULL to the notification string
    *bufPtr = 0;
  
    /////////calling/////////
  
  // Check if it's an incoming call or an SMS
    if (strstr(fonaNotificationBuffer, "RING")) {
      // Handle the incoming call
      Serial.println("Incoming call detected.");
      answerIncomingCall(); // Call answering logic (this could be embedded here)
      handleVoiceCall(); // Start handling DTMF tones (could be integrated here)
    }
  
   
    // Scan the notification string for an SMS received notification.
    // If it's an SMS message, we'll get the slot number in 'slot'
   else if (1 == sscanf(fonaNotificationBuffer, "+CMTI: " FONA_PREF_SMS_STORAGE ",%d", &slot))
    { 
       BWS = "SMS";    // current mode you want to store
   updateBWSStatus(BWS.c_str());  // <--- STORE to flash
  linkswitches = 0;

      gpsActive = false;  // Stop GPS function immediately         
      Serial.print("slot: ");
      Serial.println(slot);
  
      char callerIDbuffer[32]; // we'll store the SMS sender number in here
  
      // Retrieve SMS sender address/phone number.
      if (!fona.getSMSSender(slot, callerIDbuffer, 31))
      {
        Serial.println("Didn't find SMS message in slot!");
      }
      
      Serial.print(F("FROM: "));
      Serial.println(callerIDbuffer);
  
            ////////////////////////////////////////////////////
       String incoming = String(callerIDbuffer);

    // Remove +91 if present
     if (incoming.startsWith("+91")) {
      incoming = incoming.substring(3);
     }

     incoming.trim();

      bool isAllowedNumber = isPhoneNumberAllowed(incoming.c_str());

      //////////////////////////////////////////////////
  
      // Validate the phone number against the allowed list
      //bool isAllowedNumber = isPhoneNumberAllowed(callerIDbuffer);
  
      if (!isAllowedNumber)
      {
        
        // Retrieve SMS value.
        uint16_t smslen;
        if (fona.readSMS(slot, smsBuffer, 250, &smslen)) // pass in buffer and max len!
        {
          smsString = String(smsBuffer);
          Serial.println(smsString);
  
          // Check if the SMS command is for adding a new phone number
          if (smsString.startsWith("ADD "))
          {
            String newNumber = smsString.substring(4);
            newNumber.trim();   // VERY IMPORTANT
            addPhoneNumber(newNumber.c_str());

            // Extract the phone number to add
            //const char *newPhoneNumber = smsString.substring(4).c_str();
            //addPhoneNumber(newPhoneNumber);

            delay(2000);
            //fona.sendSMS(callerIDbuffer, "New phone number added.");
            char msg1[] = "New phone number added.";
            fona.sendSMS(callerIDbuffer, msg1);
  
            Deletesms();
            return; // Exit the function to avoid further processing
          }
          //else 
           if (smsString.startsWith("REMOVE ")) // Check for "remove" command
        {
        String removeNumber = smsString.substring(7);
        removeNumber.trim();
        removePhoneNumber(removeNumber.c_str());
        delay(2000);
        char msg2[] = "Phone number removed.";
        fona.sendSMS(callerIDbuffer, msg2);
        // Extract the phone number to remove
        //const char* numberToRemove = smsString.substring(7).c_str();
        //removePhoneNumber(numberToRemove);
        
        //fona.sendSMS(callerIDbuffer, "Phone number removed.");
        Deletesms();
      } 


  
       }
      
       Serial.println("Unauthorized phone number.");
        //fona.sendSMS(callerIDbuffer, "Unauthorized phone number.");
        delay(2000);
        char msg3[] = "Unauthorized phone number.";
        fona.sendSMS(callerIDbuffer, msg3);
        Deletesms();
        return; // Exit the function and do not proceed further with the command
      
  
      }

   
  /////////////////////////////////////////////////////////////////////////////////////////////
    
           // Retrieve SMS value.
      uint16_t smslen;
      if (fona.readSMS(slot, smsBuffer, 250, &smslen)) // pass in buffer and max len!
      {
        smsString = String(smsBuffer);
        Serial.println(smsString);
                
      }
     
  /* BWS = "SMS";    // current mode you want to store
   updateBWSStatus(BWS.c_str());  // <--- STORE to flash
  linkswitches = 0;*/
  
if (smsString == "MANUAL PUMP")   
      {
       MANUALMODEPUMP();
       //char msg4[] = "MANUAL PUMP";
       //fona.sendSMS(callerIDbuffer, msg4);   
       previousswitch = 0; 
       SWITCHSMS = "SWITCH STATUS";
       SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
       
       Deletesms();   
      }

     // else if(smsString.equalsIgnoreCase("PUMP OFF"))
      else if (smsString == "PUMP UTILITY OFF")   
      {
  
       //fona.sendSMS(callerIDbuffer, "PUMP OFF");
       //char msg5[] = "PUMP OFF";
       //fona.sendSMS(callerIDbuffer, msg5);
       previousswitch = 0;
       PUMPLOADOFF();
       SWITCHSMS = "SWITCH STATUS";
       SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
       Deletesms();
      }

      else if(smsString == "MANUAL UTILITY")   
      {
       MANUALMODEUTILITY();
       //char msg4[] = "MANUAL PUMP";
       //fona.sendSMS(callerIDbuffer, msg4);   
       previousswitch = 0; 
       SWITCHSMS = "SWITCH STATUS";
       SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
       
       Deletesms();   
      }

       else if(smsString == "MANUAL PUMP UTILITY")   
      {
       MANUALMODEPUMPUTILITY();
       //char msg4[] = "MANUAL PUMP";
       //fona.sendSMS(callerIDbuffer, msg4);   
       previousswitch = 0; 
       SWITCHSMS = "SWITCH STATUS";
       SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
       
       Deletesms();   
      }
      
      else if (smsString == "INITSTATUS")   
      {
       
      // Send SMS to all allowed numbers
      char statusMessageBuffer[255]; // Adjust size as needed
      currentStatusMessageSMS.toCharArray(statusMessageBuffer, sizeof(statusMessageBuffer));
      
      switchcontrolvar = loadSwitchControlVar();
      if(switchcontrolvar == 1)
      {
        char msg17[] = "keyactive";
        fona.sendSMS(callerIDbuffer, msg17);
      }
      else if(switchcontrolvar == 0){
        char msg18[] = "keydeactive";
        fona.sendSMS(callerIDbuffer, msg18);
      }
      delay(2000);

      for (int i = 0; i < numAllowedNumbers; i++) {
        fona.sendSMS(allowedPhoneNumbers[i], statusMessageBuffer);
      }

      
    
       
char smsBuffer[50];

  // ----- Pump1 -----
  if (pump1Counter > 0) {
    sprintf(smsBuffer, "Pump1 Remaining Time: %lu", pump1Counter);
    for (int i = 0; i < numAllowedNumbers; i++) {
      fona.sendSMS(allowedPhoneNumbers[i], smsBuffer);
    }
  }

  // ----- BPump -----
  if (Bpump1Counter > 0) {
    sprintf(smsBuffer, "BPump Remaining Time: %lu", Bpump1Counter);
    for (int i = 0; i < numAllowedNumbers; i++) {
      fona.sendSMS(allowedPhoneNumbers[i], smsBuffer);
    }
  }

  // ----- CPump -----
  if (Cpump1Counter > 0) {
    sprintf(smsBuffer, "CPump Remaining Time: %lu", Cpump1Counter);
    for (int i = 0; i < numAllowedNumbers; i++) {
      fona.sendSMS(allowedPhoneNumbers[i], smsBuffer);
    }
  }
  
       Deletesms();
      }
  
      else if (smsString == "AUTO MODE") 
      {
        //fona.sendSMS(callerIDbuffer, "AUTO MODE");
        //char msg10[] = "AUTO MODE";
        //fona.sendSMS(callerIDbuffer, msg10);
        AUTOMODE();
        previousswitch = 0;
       SWITCHSMS = "SWITCH STATUS";
       SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
        Deletesms();
      }
      else if (smsString == "AUTO MODE OFF") 
      {
        //fona.sendSMS(callerIDbuffer, "AUTO MODE OFF");
       // char msg11[] = "AUTO MODE OFF";
       // fona.sendSMS(callerIDbuffer, msg11);
        AUTOMODEOFF();
        previousswitch = 0;
        SWITCHSMS = "SWITCH STATUS";
       SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
        Deletesms();
      }
  
      else if (smsString.startsWith("ADD "))
      {
        // Extract the phone number to add
        const char *newPhoneNumber = smsString.substring(4).c_str();
        addPhoneNumber(newPhoneNumber);
        //fona.sendSMS(callerIDbuffer, "New phone number added.");
        char msg1[] = "New phone number added.";
        fona.sendSMS(callerIDbuffer, msg1);

        Deletesms();
        //return; // Exit the function to avoid further processing
      }
        else if (smsString.startsWith("REMOVE ")) // Check for "remove" command
      {
        // Extract the phone number to remove
        const char* numberToRemove = smsString.substring(7).c_str();
        removePhoneNumber(numberToRemove);
        
        //fona.sendSMS(callerIDbuffer, "Phone number removed.");
        char msg12[] = "Phone number removed.";
        fona.sendSMS(callerIDbuffer, msg12);
  
        Deletesms();
      }
  
  
        else if (smsString == "GET LOCATION")
      {
        sendLocationToUsers();
        Deletesms();
        return;
      }
  
  
  ////LOCK PASSWORD//
  /*else if (smsString.startsWith("SET PASSWORD ")) {
    // Extract the new password from the SMS
    String newPassword = smsString.substring(13); // Extract the password after "SET PASSWORD "
    
    // Check if the new password is valid (e.g., 4 digits)
    if (newPassword.length() == 4 && newPassword.toInt() != 0) {
        password = newPassword; // Update the password
        storelockPasswordInFlash(password); // Store the new password in flash memory
        //fona.sendSMS(callerIDbuffer, "Password updated successfully.");
        char msg15[] =  "Password updated successfully.";
        fona.sendSMS(callerIDbuffer, msg15);
        Serial.println("Password updated to: " + password);
    } else {
        //fona.sendSMS(callerIDbuffer, "Invalid password format. Please use a 4-digit password.");
        char msg16[] =  "Invalid password format. Please use a 4-digit password.";
        fona.sendSMS(callerIDbuffer, msg16);
    }
    Deletesms();  // Optionally delete the SMS after processing
  }*/
  
  else if (smsString.startsWith("PUMP:") ) {
      updatePumpSchedule(smsString);
      delay(200);
      pump1MissedSent = false;
      savePump1MissedFlag(false);
     // char msg21[] =  "TIMER PUMP";
     // fona.sendSMS(callerIDbuffer, msg21);
     previousswitch = 0;
     SWITCHSMS = "SWITCH STATUS";
       SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
      Deletesms();
  }

  else if (smsString.startsWith("BPUMP:") ) {
      BupdatePumpSchedule(smsString);
      delay(200);
      Bpump1MissedSent = false;
      saveBPumpMissedFlag(false);
     // char msg21[] =  "TIMER PUMP";
     // fona.sendSMS(callerIDbuffer, msg21);
     previousswitch = 0;
     SWITCHSMS = "SWITCH STATUS";
      SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
      Deletesms();
  }
  else if (smsString.startsWith("CPUMP:") ) {
      CupdatePumpSchedule(smsString);
      delay(200);
      Cpump1MissedSent = false;
      saveCPumpMissedFlag(false);
     // char msg21[] =  "TIMER PUMP";
     // fona.sendSMS(callerIDbuffer, msg21);
     previousswitch = 0;
     SWITCHSMS = "SWITCH STATUS";
     SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
      Deletesms();
  }
  
  else if (smsString.startsWith("STOP PUMP")) {
      STOPPUMP1();
      //char msg22[] =  "PAUSE PUMP";
      //fona.sendSMS(callerIDbuffer, msg22);
      previousswitch = 0;
      SWITCHSMS = "SWITCH STATUS";
       SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
      Deletesms();
    } 

    else if (smsString.startsWith("STOP BPUMP")) {
      BSTOPPUMP1();
      //char msg22[] =  "PAUSE PUMP";
     // fona.sendSMS(callerIDbuffer, msg22);
     previousswitch = 0;
     SWITCHSMS = "SWITCH STATUS";
       SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
      Deletesms();
    } 

    else if (smsString.startsWith("STOP CPUMP")) {
      CSTOPPUMP1();
      //char msg22[] =  "PAUSE PUMP";
      //fona.sendSMS(callerIDbuffer, msg22);
      previousswitch = 0;
      SWITCHSMS = "SWITCH STATUS";
       SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
      Deletesms();
    } 
  
    else if (smsString.startsWith("STOP TIMER")) {
      stoptimermode();
      //char msg24[] =  "STOP TIMER";
      //fona.sendSMS(callerIDbuffer, msg24);
      previousswitch = 0;
      SWITCHSMS = "SWITCH STATUS";
       SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
      Deletesms();
    }
    else if (smsString == ("keyactive"))
     { 
      switchcontrolvar = 1;
      storeSwitchControlVar(switchcontrolvar);
      char msg17[] = "keyactive";
      fona.sendSMS(callerIDbuffer, msg17);
      delay(2000);
      // Send SMS to all allowed numbers
      char statusMessageBuffer[255]; // Adjust size as needed
      currentStatusMessageSMS.toCharArray(statusMessageBuffer, sizeof(statusMessageBuffer));
      for (int i = 0; i < numAllowedNumbers; i++) {
        fona.sendSMS(allowedPhoneNumbers[i], statusMessageBuffer);
      }
      Deletesms();
      }
      else if (smsString == ("keydeactive"))
     { 
      switchcontrolvar = 0;
      storeSwitchControlVar(switchcontrolvar);
      char msg18[] = "keydeactive";
      fona.sendSMS(callerIDbuffer, msg18);
      delay(2000);
      // Send SMS to all allowed numbers
      char statusMessageBuffer[255]; // Adjust size as needed
      currentStatusMessageSMS.toCharArray(statusMessageBuffer, sizeof(statusMessageBuffer));
      for (int i = 0; i < numAllowedNumbers; i++) {
        fona.sendSMS(allowedPhoneNumbers[i], statusMessageBuffer);
      }
      Deletesms();
      }



     else if (smsString.startsWith("E")) { // Update SSID in a single step
    String newSSID = smsString.substring(1); // Extract the part after "E"
    newSSID.trim(); // Remove unnecessary spaces or newline characters

    if (newSSID.length() > 0) {
        updateSSID(newSSID.c_str()); // Update SSID
        WiFi.begin(newSSID.c_str(), wifi_password); // Reconnect WiFi with updated SSID
        //fona.sendSMS(callerIDbuffer, "SSID updated");
        char smsMsg[] = "SSID updated";
        fona.sendSMS(callerIDbuffer, smsMsg);
        Serial.println("SSID updated");
    } else {
        //fona.sendSMS(callerIDbuffer, "Invalid SSID");
        char smsMsg[] = "Invalid SSID";
        fona.sendSMS(callerIDbuffer, smsMsg);
        Serial.println("Invalid SSID");
    }
    loadSSID(); //RETRIVE SSID OF WIFI
  
} 
else if (smsString.startsWith("F")) { // Update WiFi Password in a single step
    String newPassword = smsString.substring(1); // Extract the part after "F"
    newPassword.trim(); // Remove unnecessary spaces or newline characters

    if (newPassword.length() > 0) {
        updatePassword(newPassword.c_str()); // Update password
        WiFi.begin(wifi_ssid, newPassword.c_str()); // Reconnect WiFi with updated password
        //fona.sendSMS(callerIDbuffer, "WiFi Password updated");
        char smsMsg[] = "WiFi Password updated";
        fona.sendSMS(callerIDbuffer, smsMsg);
        Serial.println("WiFi Password updated");
    } else {
        //fona.sendSMS(callerIDbuffer, "Invalid Password");
        char smsMsg[] = "Invalid Password";
        fona.sendSMS(callerIDbuffer, smsMsg);
        Serial.println("Invalid Password");
    }
    loadPassword(); //RETRIVE PASSWORD OF WIFI
} 

// SIMCARD AND GPS UNPLUG PASSWORD
   else if (smsString.startsWith("H")) { // Command to set the password via Bluetooth
    String newPassword = smsString.substring(1); // Extract the part after "H"
    newPassword.trim(); // Remove any unwanted spaces or newline characters

    // Check if the new password is valid (e.g., 4 digits)
    if (newPassword.length() == 4 && newPassword.toInt() != 0) {
        password = newPassword; // Update the password
        storelockPasswordInFlash(password); // Store the new password in flash memory
        //fona.sendSMS(callerIDbuffer, "System Lock Password Updated");
        char smsMsg[] = "System Lock Password Updated";
        fona.sendSMS(callerIDbuffer, smsMsg);
        Serial.println("System Lock Password Updated");
    } else {
        //fona.sendSMS(callerIDbuffer, "Invalid password — 4 digits required");
        char smsMsg[] = "Invalid password — 4 digits required";
        fona.sendSMS(callerIDbuffer, smsMsg);
        Serial.println("Invalid password — 4 digits required");
    }
}
  /////////END///////////////////

  
      
       else
      {
        // Handle invalid SMS here
        Serial.println("Invalid SMS command.");
        //fona.sendSMS(callerIDbuffer, "Invalid SMS command.");
        char msg17[] =  "Invalid SMS command.";
        fona.sendSMS(callerIDbuffer, msg17);
        Deletesms();
      }
      
  gpsActive = true;  // Resume GPS function after processing
    }
  
  }
 

  if (isAutoModeSolar) {
     TOPTANK();
    }
  
         // Update the Time library every hour
  time_t t = now();
  if (minute(t) == 0 && second(t) == 0)
  {
    digitalClockDisplay(); // Display current time (optional)
    setTimeFromGSM();      // Update time from GSM network every hour
     //isBoardRestarted = false;  // Reset the flag indicating board restart after each hour
  }
}
  

/////////2ND SMS////////////

void _2sms(){
  char *bufPtr = fonaNotificationBuffer; // handy buffer pointer
  
  if (fona.available()) // any data available from the FONA?
  {
    int slot = 1; // this will be the slot number of the SMS
    int charCount = 0;
    // Read the notification into fonaInBuffer
    do
    {
      *bufPtr = fona.read();
      Serial.write(*bufPtr);
      delay(1);
    } while ((*bufPtr++ != '\n') && (fona.available()) && (++charCount < (sizeof(fonaNotificationBuffer) - 1)));
  
    // Add a terminal NULL to the notification string
    *bufPtr = 0;

    /////////calling/////////
  
  // Check if it's an incoming call or an SMS
    if (strstr(fonaNotificationBuffer, "RING")) {
      // Handle the incoming call
      Serial.println("Incoming call detected.");
      //answerIncomingCall(); // Call answering logic (this could be embedded here)
      //handleVoiceCall(); // Start handling DTMF tones (could be integrated here)
    }
    // Scan the notification string for an SMS received notification.
    // If it's an SMS message, we'll get the slot number in 'slot'
   else if (1 == sscanf(fonaNotificationBuffer, "+CMTI: " FONA_PREF_SMS_STORAGE ",%d", &slot))
    { 
       BWS = "SMS";    // current mode you want to store
   updateBWSStatus(BWS.c_str());  // <--- STORE to flash
  linkswitches = 0;

      gpsActive = false;  // Stop GPS function immediately         
      Serial.print("slot: ");
      Serial.println(slot);
  
      char callerIDbuffer[32]; // we'll store the SMS sender number in here
  
      // Retrieve SMS sender address/phone number.
      if (!fona.getSMSSender(slot, callerIDbuffer, 31))
      {
        Serial.println("Didn't find SMS message in slot!");
      }
      
      Serial.print(F("FROM: "));
      Serial.println(callerIDbuffer);
  
      // Validate the phone number against the allowed list
      bool isAllowedNumber = isPhoneNumberAllowed(callerIDbuffer);
  
      if (!isAllowedNumber)
      {
        // Retrieve SMS value.
        uint16_t smslen;
        if (fona.readSMS(slot, smsBuffer, 250, &smslen)) // pass in buffer and max len!
        {
          smsString = String(smsBuffer);
          Serial.println(smsString);
       }
  
        Serial.println("Unauthorized phone number.");
        //fona.sendSMS(callerIDbuffer, "Unauthorized phone number.");
        char msg3[] = "Unauthorized phone number.";
        fona.sendSMS(callerIDbuffer, msg3);
        Deletesms();
        return; // Exit the function and do not proceed further with the command
      }
   
  /////////////////////////////////////////////////////////////////////////////////////////////
    
           // Retrieve SMS value.
      uint16_t smslen;
      if (fona.readSMS(slot, smsBuffer, 250, &smslen)) // pass in buffer and max len!
      {
        smsString = String(smsBuffer);
        Serial.println(smsString);        
      }
          
       if(smsString == "YES")   
      {
       isLocked = true;  // Lock the system
       storeLockStatus(isLocked);
       smstimer = 0;
       gpstimer = 0;
       Deletesms();   
      }
      else if(smsString == "NO")   
      {
       isLocked = false;  // Lock the system
       storeLockStatus(isLocked);
       smstimer = 1;
       gpstimer = 1;
       Deletesms();   
       
      
      }
      else if(smsString == "UNLOCK")   
      {
       isLocked = false;  // Lock the system
       storeLockStatus(isLocked);
        float currentLatitude, currentLongitude;
                if (fona.getGPS(&currentLatitude, &currentLongitude)) {
                    char fullLatitude[15];  // Buffer for full latitude
                    char fullLongitude[15]; // Buffer for full longitude

                    // No significant location change, continue normal operation
                    snprintf(fullLatitude, sizeof(fullLatitude), "%.6f", currentLatitude);
                    snprintf(fullLongitude, sizeof(fullLongitude), "%.6f", currentLongitude);
                    char locationMsg[100];
                    delay(1000);
                    snprintf(locationMsg, sizeof(locationMsg), "Click the link to view the location: https://maps.google.com/?q=%.6f,%.6f", currentLatitude, currentLongitude);

                    // Send SMS to all allowed numbers
                    for (int i = 0; i < numAllowedNumbers; i++) {
                        fona.sendSMS(allowedPhoneNumbers[i], locationMsg);
                    }

                    // Optionally update previous coordinates
                    previousLatitude = currentLatitude;
                    previousLongitude = currentLongitude;
                    storePreviousLocation(previousLatitude, previousLongitude);
                }
       DRIVES_STATUS = 1;
       loadupdatedSMSStatus();
       Previousstate();
       smstimer = 1;
       gpstimer = 1;
       signal();
       Deletesms();   
      }
      else if (smsString == "INITSTATUS")   
      {
        if(isLocked == true){
        //fona.sendSMS(callerIDbuffer, "Searching");
      char SEA[] = "searching.";
        //fona.sendSMS(callerIDbuffer, msg17);
        for (int i = 0; i < numAllowedNumbers; i++) {
        fona.sendSMS(allowedPhoneNumbers[i], SEA);}
        }else
        {
          char SEA[] = "Searching";
        //fona.sendSMS(callerIDbuffer, msg17);
        for (int i = 0; i < numAllowedNumbers; i++) {
        fona.sendSMS(allowedPhoneNumbers[i], SEA);}
        }
  
       Deletesms();
      }
       else
      {
        Deletesms();
      }  
  gpsActive = true;  // Resume GPS function after processing
    }
   }
}
/*****************************************************************************************
             STORE USER REGISTER PHONE NUMBER
 *****************************************************************************************/
/*void addPhoneNumber(const char *phoneNumber) {
    SPI.begin();
  if (numAllowedNumbers < MAX_ALLOWED_NUMBERS) {
    uint32_t address = (numAllowedNumbers == 0) ? PHONE_NUMBER_ADDRESS_1 : PHONE_NUMBER_ADDRESS_2;
    digitalWrite(CS_1, LOW); // Select the flash memory
    size_t phoneNumberLength = strlen(phoneNumber) + 1;
    uint8_t dataBuffer[phoneNumberLength]; // Dynamically allocate buffer based on phone number length
    // Copy the phone number data to the buffer as bytes
    strncpy((char *)dataBuffer, phoneNumber, phoneNumberLength);
    // Write bytes to flash
    for (size_t i = 0; i < phoneNumberLength; i++) {
      flash.writeByte(address + i, dataBuffer[i]);
    }
    digitalWrite(CS_1, HIGH); // Deselect the flash memory
    strcpy(allowedPhoneNumbers[numAllowedNumbers], phoneNumber);
    numAllowedNumbers++;    
    Serial.print(F("Added new phone number: "));
    Serial.println(phoneNumber);
    SPI.end();
  } else {
    Serial.println(F("Maximum number of allowed phone numbers reached."));
  }
  loadAllowedPhoneNumbers();
}*/

void addPhoneNumber(const char *phoneNumber) {
  SPI.begin();

  if (numAllowedNumbers >= MAX_ALLOWED_NUMBERS) {
    Serial.println("Max numbers reached");
    SPI.end();
    return;
  }

  // Normalize number (remove +91)
  String num = String(phoneNumber);
  if (num.startsWith("+91")) num = num.substring(3);
  num.trim();

  uint32_t address = (numAllowedNumbers == 0) ? PHONE_NUMBER_ADDRESS_1 : PHONE_NUMBER_ADDRESS_2;

  digitalWrite(CS_1, LOW);

  flash.eraseSector(address);   //  IMPORTANT FIX

  for (int i = 0; i < num.length(); i++) {
    flash.writeByte(address + i, num[i]);
  }

  flash.writeByte(address + num.length(), '\0'); // null terminate

  digitalWrite(CS_1, HIGH);

  strcpy(allowedPhoneNumbers[numAllowedNumbers], num.c_str());
  numAllowedNumbers++;

  Serial.print("Stored: ");
  Serial.println(num);
  
  loadAllowedPhoneNumbers();
  SPI.end();

  
}

/*****************************************************************************************
             RETRIVE STORED USER PHONE NUMBER
 *****************************************************************************************/
/*void loadAllowedPhoneNumbers() {
  SPI.begin();
     digitalWrite(CS_1, LOW); // Select the flash memory
    // Load allowed phone numbers
    for (int i = 0; i < sizeof(allowedPhoneNumbers[0]); i++) {
    allowedPhoneNumbers[0][i] = flash.readByte(PHONE_NUMBER_ADDRESS_1 + i);
    }
    for (int i = 0; i < sizeof(allowedPhoneNumbers[1]); i++) {
    allowedPhoneNumbers[1][i] = flash.readByte(PHONE_NUMBER_ADDRESS_2 + i);
    }

    digitalWrite(CS_1, HIGH); // Deselect the flash memory
   // Calculate the number of allowed phone numbers
    numAllowedNumbers = (allowedPhoneNumbers[0][0] != '\0') + (allowedPhoneNumbers[1][0] != '\0');
    SPI.end();
  }*/

  void loadAllowedPhoneNumbers() {
  SPI.begin();

  digitalWrite(CS_1, LOW);

  for (int i = 0; i < 2; i++) {
    uint32_t addr = (i == 0) ? PHONE_NUMBER_ADDRESS_1 : PHONE_NUMBER_ADDRESS_2;

    for (int j = 0; j < 20; j++) {
      char c = flash.readByte(addr + j);

      if (c == 0xFF || c == '\0') {
        allowedPhoneNumbers[i][j] = '\0';
        break;
      }

      allowedPhoneNumbers[i][j] = c;
    }
  }

  digitalWrite(CS_1, HIGH);
  SPI.end();

  numAllowedNumbers = 0;

  if (allowedPhoneNumbers[0][0] != '\0') numAllowedNumbers++;
  if (allowedPhoneNumbers[1][0] != '\0') numAllowedNumbers++;

  Serial.println("Loaded Numbers:");
  Serial.println(allowedPhoneNumbers[0]);
  Serial.println(allowedPhoneNumbers[1]);
}

/*****************************************************************************************
             USER PHONE IS REGISTERED
 *****************************************************************************************/
/*bool isPhoneNumberAllowed(const char *phoneNumber) {
  SPI.begin();
    for (int i = 0; i < numAllowedNumbers; i++) {
    if (strcmp(allowedPhoneNumbers[i], phoneNumber) == 0) {
      return true;
    }
  }
  return false;
  SPI.end();
}*/

bool isPhoneNumberAllowed(const char *phoneNumber) {
  String incoming = String(phoneNumber);

  if (incoming.startsWith("+91")) incoming = incoming.substring(3);
  incoming.trim();

  for (int i = 0; i < numAllowedNumbers; i++) {
    if (incoming.equals(allowedPhoneNumbers[i])) {
      return true;
    }
  }
  return false;
}
/*****************************************************************************************
             DELETE USER REGISTERED PHONE NUMBER
 *****************************************************************************************/
/*void removePhoneNumber(const char *phoneNumber) {
  SPI.begin();
  // Search for the phone number in the list
  for (int i = 0; i < numAllowedNumbers; i++) {
    if (strcmp(allowedPhoneNumbers[i], phoneNumber) == 0) {
      uint32_t eraseAddress = (i == 0) ? PHONE_NUMBER_ADDRESS_1 : PHONE_NUMBER_ADDRESS_2;
      digitalWrite(CS_1, LOW); // Select the flash memory
      flash.eraseSector(eraseAddress);
      //flash.eraseBlock32K(eraseAddress);
      digitalWrite(CS_1, HIGH); // Deselect the flash memory
      for (int j = i; j < numAllowedNumbers - 1; j++) {
        strcpy(allowedPhoneNumbers[j], allowedPhoneNumbers[j + 1]);
      }
      numAllowedNumbers--;
      Serial.print(F("Removed phone number: "));
      Serial.println(phoneNumber);
      return;
      SPI.end();
    }
  }
  loadAllowedPhoneNumbers();
  Serial.println(F("Phone number not found in the allowed list."));
}*/

void removePhoneNumber(const char *phoneNumber) {
  SPI.begin();

  String num = String(phoneNumber);
  if (num.startsWith("+91")) num = num.substring(3);
  num.trim();

  for (int i = 0; i < numAllowedNumbers; i++) {

    if (num.equals(allowedPhoneNumbers[i])) {

      uint32_t addr = (i == 0) ? PHONE_NUMBER_ADDRESS_1 : PHONE_NUMBER_ADDRESS_2;

      digitalWrite(CS_1, LOW);
      flash.eraseSector(addr);
      digitalWrite(CS_1, HIGH);

      allowedPhoneNumbers[i][0] = '\0';

      Serial.print("Removed: ");
      Serial.println(num);

      break;
    }
  }
  loadAllowedPhoneNumbers();
  SPI.end();
  
}


/*****************************************************************************************
            DISPLAYING THE CURRENT TIME ON SERIAL (PUTTY) FUNCTION
 *****************************************************************************************/
void digitalClockDisplay()
{
  // Print the current time in the format "HH:MM:SS"
  Serial.print(hour());
  printDigits(minute());
  printDigits(second());
  Serial.println();
}

/*****************************************************************************************
            DISPLAYING THE CURRENT TIME ON SERIAL (PUTTY) FUNCTION
 *****************************************************************************************/
void printDigits(int digits)
{
  // Print leading 0s if the number is less than 10
  if (digits < 10)
  {
    Serial.print('0');
  }
  Serial.print(digits);
}

/*****************************************************************************************
            SETTING THE TIME AND DATE FROM NETWORK
 *****************************************************************************************/
void setTimeFromGSM()
{
  // If the time has been set from SMS, do not update the time from GSM network
  if (isTimeSetFromSMS)
  {
    // Reset the flag so that next time it can be updated from GSM network
    isTimeSetFromSMS = false;
    return;
  }

  // Send AT command to retrieve date and time information from the SIMCOM modem
  fonaSerial->println("AT+CCLK?");

  // Wait for the response from the modem
  delay(500);

  // Read and parse the response
  while (fonaSerial->available())
  {
    String response = fonaSerial->readStringUntil('\n');
    response.trim(); // Remove leading/trailing whitespaces

    // Extract the date and time information from the response string
    if (response.startsWith("+CCLK:"))
    {
      // Example response: +CCLK: "21/07/07,12:34:56+08"

      // Extract the date and time substring
      String dateTimeStr = response.substring(response.indexOf('"') + 1, response.lastIndexOf('"'));

      // Extract the date substring
      String dateStr = dateTimeStr.substring(0, dateTimeStr.indexOf(','));

      // Extract the time substring
      String timeStr = dateTimeStr.substring(dateTimeStr.indexOf(',') + 1);

      // Parse the values and set the system time using setTime() function
      int year = dateStr.substring(0, 2).toInt() + 2000;
      int month = dateStr.substring(3, 5).toInt();
      int day = dateStr.substring(6, 8).toInt();
      int hour = timeStr.substring(0, 2).toInt();
      int minute = timeStr.substring(3, 5).toInt();
      int second = timeStr.substring(6, 8).toInt();

      setTime(hour, minute, second, day, month, year);

      Serial.print("Time set from GSM: ");
      Serial.print(day); Serial.print("/"); Serial.print(month); Serial.print("/"); Serial.print(year);
      Serial.print(" ");
      Serial.print(hour); Serial.print(":"); Serial.print(minute); Serial.print(":"); Serial.println(second);

      break; // Exit the loop after processing the response
    }
  }
}

/*****************************************************************************************
           DELETING THE STORED SMS FROM THE SIMCARD MEMORY
 *****************************************************************************************/
void Deletesms()
{ 
  fona.print("AT+CMGD=1,4\r\n");
}

/*****************************************************************************************
           GETTING THE SIMCARD OPERATOR INFORMATION
 *****************************************************************************************/
void configureNetworkSettings() {
  // Send AT command to get the SIM operator
  char cmd9[] = "AT+COPS?";
  char reply9[] = "+COPS:";
  //fona.sendCheckReply(cmd9, reply9);
  if (fona.sendCheckReply(cmd9, reply9)) {
    // Successfully received operator information
    while (Serial.available()) {
      String response = Serial.readStringUntil('\n');
      response.trim();

      // Debug: Print received response
      Serial.println("Received response: " + response);

      // Example response: +COPS: 0,2,"40445",7
      if (response.startsWith("+COPS:") && response.indexOf(",") != -1) {
        int secondCommaIndex = response.indexOf(",", response.indexOf(",") + 1);
        int thirdCommaIndex = response.indexOf(",", secondCommaIndex + 1);

        if (thirdCommaIndex != -1) {
          String operatorName = response.substring(secondCommaIndex + 1, thirdCommaIndex);

          // Debug: Print extracted operator name
          Serial.println("Extracted operator name: " + operatorName);

          // Trim leading and trailing whitespaces
          operatorName.trim();

          // Find the corresponding network settings
          for (int i = 0; i < sizeof(networkSettings) / sizeof(networkSettings[0]); i++) {
            if (operatorName.equalsIgnoreCase(networkSettings[i].apn)) {
              setNetworkSettings(networkSettings[i]);
              return;
            }
          }

          break;
        }
      }
    }
  }
}

/*****************************************************************************************
           GETTING THE SIMCARD OPERATOR INFORMATION
 *****************************************************************************************/
void setNetworkSettings(const NetworkSettings& settings) {
  // Use settings.apn, settings.username, and settings.password as needed
  // For example, you might set these values for your GSM module here
  Serial.print("Setting APN: ");
  Serial.println(settings.apn);
  Serial.print("Setting Username: ");
  Serial.println(settings.username);
  Serial.print("Setting Password: ");
  Serial.println(settings.password);
  // Add code to apply these settings to your GSM module
}

/*****************************************************************************************
           SIMCARD DETECTION FUNCTION
 *****************************************************************************************/
bool isSIMCardInserted() {
  String response;
  fona.println("AT+CPIN?");
  delay(100);

  unsigned long start = millis();
  while (millis() - start < 200) {
    while (fona.available()) {
      response = fona.readString();
      Serial.println(response);  // Print the response for debugging
      if (response.indexOf("READY") != -1) {
        return true;  // SIM card is present and ready
      }
      if (response.indexOf("NOT INSERTED") != -1) {
        return false;  // SIM card is not inserted
      }
    }
  }

  return false;  // No response or SIM card not present
}

/*****************************************************************************************
           GETTING THE SIGNAL STRENGTH IN PERCENTAGE (%)
 *****************************************************************************************/
int get_network() {
  String buff;
  unsigned int result, index1, index2, timeout = 0;
  // Send command and wait for response
  fona.println("AT+CSQ");
  delay(100);

  unsigned long start = millis();
  while (millis() - start < 200) {
    while (fona.available()) {
      buff = fona.readString();
      timeout = 1;
      break;
    }
  }

  if (timeout == 0) {
    Serial.println("No response from AT+CSQ command.");
    return 0;
  }

  Serial.println("AT+CSQ response:");
  Serial.println(buff);

  // Find and parse the signal strength from the response
  index1 = buff.indexOf("+CSQ: ");
  if (index1 == -1) {
    Serial.println("Error parsing signal strength. +CSQ header not found.");
    return 0;
  }

  index1 += 6; // Move index to start of signal strength
  index2 = buff.indexOf(",", index1);
  if (index2 == -1) {
    Serial.println("Error parsing signal strength. Comma not found.");
    return 0;
  }

  String signalStr = buff.substring(index1, index2);
  signalStr.trim();
  result = signalStr.toInt();

  Serial.print("Signal strength raw value: ");
  Serial.println(result);

   if (result >= 2 && result <= 9) {
    return 10;
  } else if (result >= 10 && result <= 19) {
    return 50;
  } else if (result >= 20 && result <= 31) {
    return 99; //THIS IS %. NOT -99
  }

  return 0;
}

/*****************************************************************************************
           DISPLAYING THE SIGNAL BARS ON LCD
 *****************************************************************************************/
void display_network(int signalStrength) {
 
  if(signalStrength == 10)
  {
  lcd.createChar(0, indicator0);
  lcd.setCursor(15, 0);
  lcd.write(0);
  }

  else if(signalStrength == 50)
  {
  lcd.createChar(0, indicator1);
  lcd.setCursor(15, 0);
  lcd.write(0);
  }

  else if(signalStrength == 99)
  {
  lcd.createChar(0, indicator2);
  lcd.setCursor(15, 0);
  lcd.write(0);
  }

}

/*****************************************************************************************
           NETWORK SIGNAL FUNCTION
 *****************************************************************************************/
void signal()
{
    if (isSIMCardInserted()) {
      Serial.println("SIM card is present.");
      int signalStrength = get_network();
      display_network(signalStrength);
      isLocked = false;  // unLock the system
      storeLockStatus(isLocked);  // Save the updated lock status
      
    } else {
      lcd.createChar(0, Nosignal);
      lcd.setCursor(15, 0);
      lcd.write(0);
      Serial.println("SIM card is not inserted.");
      isLocked = true;  // Lock the system
      storeLockStatus(isLocked);  // Save the updated lock status
      
    }
}

/*****************************************************************************************
           ANAWERING THE INCOMING CALL
 *****************************************************************************************/
/*void handleIncomingCallCheck() {
  static char buf[64];
  static int index = 0;

  while (fona.available()) {
    char c = fona.read();
    if (c == '\n' || index >= 63) {
      buf[index] = '\0';
      index = 0;

      // Detect call start
      if (strstr(buf, "RING")) {
        Serial.println("Incoming call detected");
        answerIncomingCall();
        handleVoiceCall();
      }

      // Detect caller number (optional, +CLIP)
      else if (strstr(buf, "+CLIP")) {
        // later you can extract number if needed
        Serial.println(buf);
      }
    }
    else {
      buf[index++] = c;
    }
  }
}*/

/*****************************************************************************************
           ANAWERING THE INCOMING CALL/ PICKING UP THE CALL
 *****************************************************************************************/
void answerIncomingCall() {
    Serial.println("Answering incoming call...");
    //fona.sendCheckReply("ATA", "OK"); // Answer the call
    char cmd7[] = "ATA";
  char reply7[] = "OK";
  fona.sendCheckReply(cmd7, reply7);
}

/*****************************************************************************************
           LISTENING THE INPUT OF THE USER
 *****************************************************************************************/
void handleVoiceCall() {
   
    Serial.println("Listening for DTMF tones...");
   
    // Add a delay after answering the call to stabilize
    delay(2000); // Wait for 2 seconds

    while (true) { // Run until the call ends
        char tone = waitForDTMFTone(); // Wait for DTMF tone
        if (tone != '\0') { // Check if a valid tone was received
            Serial.print("Received DTMF tone: ");
            Serial.println(tone);
            handleVoiceCommand(tone); // Handle the received tone
            hangUpCall(); // Hang up the call after processing the tone
            break; // Break after processing the tone
        }
        delay(500); // Add a small delay to avoid rapid looping
    }
}

/*****************************************************************************************
           ENTERING THE NUMBERS 0-9 AND * # BY THE USER
 *****************************************************************************************/
// Function to wait for DTMF tones
char waitForDTMFTone() {
    // Flush any previous data in the buffer
    while (fona.available()) {
        fona.read();
    }

    // Wait for DTMF tone (you might need to adjust timeout values)
    unsigned long startTime = millis();
    while (millis() - startTime < 5000) { // Wait for up to 5 seconds
        if (fona.available()) {
            char c = fona.read();

            // Check if the character is a DTMF tone (0-9, *, #)
            if ((c >= '0' && c <= '9') || c == '*' || c == '#') {
                return c; // Return detected DTMF tone
            }
        }
    }
    return '\0'; // Return null character if no tone was detected
}

/*****************************************************************************************
           EXECUTING THE DTMF TONE
 *****************************************************************************************/
void handleVoiceCommand(char dtmfTone) {
  switch (dtmfTone) {
      case '1':
          Serial.println("Activating MANUAL PUMP");
          MANUALMODEPUMP();
          sendDTMFTone('1');
          break;
      case '2':
          Serial.println("Activating PUMP UTILITY OFF");
          PUMPLOADOFF();
          sendDTMFTone('2');
          break;
      case '3':
          Serial.println("Activating UTILITY");
          MANUALMODEUTILITY();
          sendDTMFTone('3');
          break;
      case '4':
          Serial.println("Activating PUMP UTILITY");
          MANUALMODEPUMPUTILITY();
          sendDTMFTone('4');
          break;


      case '5':
          Serial.println("Activating AUTO MODE");
          AUTOMODE();
          sendDTMFTone('5');
          break;

      case '6':
          Serial.println("Activating AUTO MODE OFF");
          AUTOMODEOFF();
          sendDTMFTone('6');
          break;
      
      default:
          Serial.println("Invalid DTMF tone.");
          break;
  }
}

/*****************************************************************************************
           SENDING THE DTMF TONE TO SIMCOM
 *****************************************************************************************/
// Function to send DTMF tone
void sendDTMFTone(char tone) {
    char command[20];
    snprintf(command, sizeof(command), "AT+VTS=%c", tone);
    char reply6[] = "OK";
    if (fona.sendCheckReply(command, reply6)) {
        Serial.print("Sent DTMF tone: ");
        Serial.println(tone);
    } else {
        Serial.println("Failed to send DTMF tone.");
    }
}

/*****************************************************************************************
           HANGUP THE CALL 
 *****************************************************************************************/
void hangUpCall() {
    Serial.println("Hanging up the call...");
    //fona.sendCheckReply("ATH", "OK"); // Send the hang up command
    char cmd8[] = "ATH";
  char reply8[] = "OK";
  fona.sendCheckReply(cmd8, reply8);
}

/*****************************************************************************************
           STORE LAST STATE OF MODE'S
 *****************************************************************************************/
void updateSMSStatus(const char *newStatus) {
  SPI.begin();
//SPI.beginTransaction(SPISettings(SPI_CLOCK_DIV2, LSBFIRST, SPI_MODE0));
  uint32_t smsStatusAddress = SMS_STATUS_ADDRESS;
  digitalWrite(CS_1, LOW); // Select the flash memory
  // Erase the sector before writing new data
  flash.eraseSector(smsStatusAddress);
  // Write the actual characters of the new SMS status
  for (int i = 0; i < strlen(newStatus); i++) {
    flash.writeByte(smsStatusAddress + i, newStatus[i]);
  }
  
  // Null-terminate the string
  flash.writeByte(SMS_STATUS_ADDRESS + strlen(newStatus), '\0');
  digitalWrite(CS_1, HIGH); // Deselect the flash memory
  // Print debug information
  Serial.println("Updated SMS Status in Flash:");
  Serial.println(newStatus);
  Serial.println(SMS_STATUS_ADDRESS);
  //delay(1000); //1000
  // Add additional debug information if needed
  SPI.endTransaction();
}

/*****************************************************************************************
           RETERIVE LAST STATE OF MODE'S
 *****************************************************************************************/
int loadupdatedSMSStatus(){
  SPI.begin();
     digitalWrite(CS_1, LOW); // Select the flash memory
    // Load the actual characters of the SMS string
    uint32_t smsStatusAddress = SMS_STATUS_ADDRESS;
    for (int i = 0; i < sizeof(smsBuffer); i++) {
    smsBuffer[i] = flash.readByte(smsStatusAddress + i);
    // Print ASCII values for debugging
    Serial.print((int)smsBuffer[i]);
    Serial.print(" ");
  }
    Serial.println(); // Print a new line for better readability
    digitalWrite(CS_1, HIGH); // Deselect the flash memory
   // Null-terminate the loaded string
    smsBuffer[sizeof(smsBuffer) - 1] = '\0';
    // Print debug information
    Serial.println("Loaded SMS Status from Flash during initialization:");
    Serial.println(smsBuffer);
    SPI.end();
    return 0;  // Return a default value
}

/*****************************************************************************************
           LAST STATE OF MODE'S
 *****************************************************************************************/
void Previousstate()  //void test()
{
      smstimer = 1;
       gpstimer = 1;
  if (strcmp(smsBuffer, "MANUAL PUMP") == 0)   
  { 
     MANUALMODEPUMP();   
     //previousswitch = 1;  
  }

  else if (strcmp(smsBuffer, "PUMP UTILITY OFF") == 0)   
  { 
     PUMPLOADOFF(); 
     //previousswitch = 2;    
  }

  else if (strcmp(smsBuffer, "MANUAL UTILITY") == 0)   
  { 
     MANUALMODEUTILITY();  
     //previousswitch = 2;    
  }

  else if (strcmp(smsBuffer, "MANUAL PUMP UTILITY") == 0)   
  { 
     MANUALMODEPUMPUTILITY();  
     //previousswitch = 2;    
  }

  else if(strcmp(smsBuffer, "AUTO MODE") == 0)
  {
    AUTOMODE();
    //previousswitch = 3;
  }

  else if(strcmp(smsBuffer, "AUTO MODE OFF") == 0)
  {
    AUTOMODEOFF();
    //previousswitch = 4;
  }

  else if(strcmp(smsBuffer, "TIMER PUMP") == 0)
  {
  if(pump1Counter >= 1)
  {
  pump1Running = true;
  TIMERMODEPUMP();
  Serial.println("Pump started.");
  }
  else if(Bpump1Counter >= 1)
  {
  Bpump1Running = true;
  TIMERMODEPUMP();
  Serial.println("BPump started.");
  }
  else if(Cpump1Counter >= 1)
  {
  Cpump1Running = true;
  TIMERMODEPUMP();
  Serial.println("CPump started.");
  }
  else{
    TIMEROFF();
  }
  }
   else if(strcmp(smsBuffer, "STOP PUMP") == 0)
  {
    STOPPUMP1();
    /*logicActivated = true;
    selectedLogic = 4;*/
  }

  else if(strcmp(smsBuffer, "STOP BPUMP") == 0)
  {
    BSTOPPUMP1();
    /*logicActivated = true;
    selectedLogic = 5;*/
  }

  else if(strcmp(smsBuffer, "STOP CPUMP") == 0)
  {
    CSTOPPUMP1();
    /*logicActivated = true;
    selectedLogic = 6;*/
  }

  else if(strcmp(smsBuffer, "TIMER MODE OFF") == 0)
  {
    TIMERMODEOFF();
  }

  else if(strcmp(smsBuffer, "TIMER OFF") == 0)
  {
    TIMEROFF();
  }   
}

/*****************************************************************************************
           STORE KEY ACTIVE OR DEACTIVE
 *****************************************************************************************/
void storeSwitchControlVar(int value) {
  SPI.begin();
  digitalWrite(CS_1, LOW);
  flash.eraseSector(SWITCHCONTROLVAR_ADDRESS); // Erase sector before writing
  flash.writeByte(SWITCHCONTROLVAR_ADDRESS, (uint8_t)(value & 0xFF)); // store as byte
  digitalWrite(CS_1, HIGH);
  SPI.end();
  Serial.println("Stored switchcontrolvar to Flash.");
  Serial.println(switchcontrolvar);
}

/*****************************************************************************************
           RETERIVE KEY ACTIVE OR DEACTIVE
 *****************************************************************************************/
int loadSwitchControlVar() {
  SPI.begin();
  digitalWrite(CS_1, LOW);
  uint8_t storedValue = flash.readByte(SWITCHCONTROLVAR_ADDRESS);
  digitalWrite(CS_1, HIGH);
  SPI.end();
  Serial.print("Loaded switchcontrolvar from Flash: ");
  Serial.println(storedValue);
  return (int)storedValue;
}

/*****************************************************************************************
           DISPLAYING MODE'S SELECTION ON LCD
 *****************************************************************************************/
void DISPLAYMODES(){
 
if(selectedLogic == 0)
{
            lcd.setCursor(0, 1);
            lcd.print("               ");

            lcd.setCursor(6, 0);
            lcd.print("MANUAL");//"M SOLAR MANUAL"  
            lcd.setCursor(0, 1);
            lcd.print("PUMP");//"M SOLAR MANUAL"    
 }

 if(selectedLogic == 1)
{
            lcd.setCursor(0, 1);
            lcd.print("               ");

            lcd.setCursor(6, 0);
            lcd.print("MANUAL");//"M SOLAR MANUAL"  
            lcd.setCursor(0, 1);
            lcd.print("UTILITY");//"M SOLAR MANUAL"    
 }

 if(selectedLogic == 2)
{
            lcd.setCursor(0, 1);
            lcd.print("               ");

            lcd.setCursor(6, 0);
            lcd.print("MANUAL");//"M SOLAR MANUAL"  
            lcd.setCursor(0, 1);
            lcd.print("PUMP UTILITY");//"M SOLAR MANUAL"    
 }
if(selectedLogic == 3) 
{
            lcd.setCursor(0, 1);
            lcd.print("               ");
            
            lcd.setCursor(6, 0);
            lcd.print("AUTO");
            //lcd.setCursor(0, 1);
            //lcd.print("AUTO MODE ON");
}

}

/*****************************************************************************************
           MODE'S SELECTION THROUGH SWITCH
 *****************************************************************************************/
void performLogic(int logicNumber, bool activate) {
 Serial.println(logicNumber);   // move this OUTSIDE the switch body

  switch (logicNumber) {
    case 0:
      if (activate) {
        MANUALMODEPUMP();
        linkswitches = 1;

        delay(2000);
        if (BWS == "SMS") {
          // Set global String, convert to char buffer and send
          SWITCHSMS = "SWITCHMANUALPUMPON";
          SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], fonaMsgBuffer);
          }

          delay(2000);
          currentStatusMessageSMS.toCharArray(statusMessageBuffer, sizeof(statusMessageBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], statusMessageBuffer);
          }
        }
      } else {
        PUMPLOADOFF();
        linkswitches = 2;

        delay(2000);
        if (BWS == "SMS") {
          SWITCHSMS = "SWITCHMANUALPUMPUTILITYOFF";
          SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], fonaMsgBuffer);
          }

          delay(2000);
          currentStatusMessageSMS.toCharArray(statusMessageBuffer, sizeof(statusMessageBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], statusMessageBuffer);
          }
        }
      }
      break;


      case 1:
      if (activate) {
        MANUALMODEUTILITY();
        linkswitches = 3;

        delay(2000);
        if (BWS == "SMS") {
          // Set global String, convert to char buffer and send
          SWITCHSMS = "SWITCHMANUALUTILITYON";
          SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], fonaMsgBuffer);
          }

          delay(2000);
          currentStatusMessageSMS.toCharArray(statusMessageBuffer, sizeof(statusMessageBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], statusMessageBuffer);
          }
        }
      } else {
        PUMPLOADOFF();
        linkswitches = 2;

        delay(2000);
        if (BWS == "SMS") {
          SWITCHSMS = "SWITCHMANUALPUMPUTILITYOFF";
          SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], fonaMsgBuffer);
          }

          delay(2000);
          currentStatusMessageSMS.toCharArray(statusMessageBuffer, sizeof(statusMessageBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], statusMessageBuffer);
          }
        }
      }
      break;
     
      case 2:
      if (activate) {
        MANUALMODEPUMPUTILITY();
        linkswitches = 4;

        delay(2000);
        if (BWS == "SMS") {
          // Set global String, convert to char buffer and send
          SWITCHSMS = "SWITCHMANUALPUMPUTILITYON";
          SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], fonaMsgBuffer);
          }

          delay(2000);
          currentStatusMessageSMS.toCharArray(statusMessageBuffer, sizeof(statusMessageBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], statusMessageBuffer);
          }
        }
      } else {
        PUMPLOADOFF();
        linkswitches = 2;

        delay(2000);
        if (BWS == "SMS") {
          SWITCHSMS = "SWITCHMANUALPUMPUTILITYOFF";
          SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], fonaMsgBuffer);
          }

          delay(2000);
          currentStatusMessageSMS.toCharArray(statusMessageBuffer, sizeof(statusMessageBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], statusMessageBuffer);
          }
        }
      }
      break;



    case 3:
      if (activate) {
        AUTOMODE();
        linkswitches = 5;

        delay(2000);
        if (BWS == "SMS") {
          SWITCHSMS = "SWITCHAUTOON";
          SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], fonaMsgBuffer);
          }

          delay(2000);
          currentStatusMessageSMS.toCharArray(statusMessageBuffer, sizeof(statusMessageBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], statusMessageBuffer);
          }
        }
      } else {
        AUTOMODEOFF();
        linkswitches = 6;

        delay(2000);
        if (BWS == "SMS") {
          SWITCHSMS = "SWITCHAUTOOFF";
          SWITCHSMS.toCharArray(fonaMsgBuffer, sizeof(fonaMsgBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], fonaMsgBuffer);
          }

          delay(2000);
          currentStatusMessageSMS.toCharArray(statusMessageBuffer, sizeof(statusMessageBuffer));
          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], statusMessageBuffer);
          }
        }
      }
      break;

    default:
      Serial.println("Invalid Logic Number");
      break;
  } // end switch
}

/*****************************************************************************************
           TOP SENSOR
 *****************************************************************************************/
bool isWaterPresent() // PUMP TOP TANK SENSOR1(TOP)
{
  return digitalRead(WATER_SENSORTOP_PIN) == HIGH; 
}

/*****************************************************************************************
           MIDDLE SENSOR
 *****************************************************************************************/
bool isWaterPresent2() // PUMP TOP TANK SENSOR2(MIDDLE)
{
  return digitalRead(WATER_SENSORTOP_PIN2) == HIGH; 
}

/*****************************************************************************************
           COMMON MANUAL MODE PUMP ON FUNCTION
 *****************************************************************************************/
void MANUALMODEPUMP(){
  digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
  digitalWrite(DRIVES_PIN2_OUTPUT, LOW);
  delay(500);

  digitalWrite(DRIVES_PIN1_OUTPUT, HIGH);
  digitalWrite(DRIVES_PIN2_OUTPUT, LOW);

    char USERMESSAGE[] = "MANUAL PUMP ON";
for (int i = 0; i < numAllowedNumbers; i++) {
  fona.sendSMS(allowedPhoneNumbers[i], USERMESSAGE);
}
  
  lcd.setCursor(0, 0);
  lcd.print("               ");
  //delay(500);
  lcd.setCursor(0, 0);
  lcd.print("MANUAL ON");
  //delay(500);
  //SerialBT.print("MANUAL");
  Serial.println("MANUAL PUMP");
  updateSMSStatus("MANUAL PUMP");
  isAutoModeSolar = false;
  DRIVES_STATUS = 1;
  currentMode = "MANUAL PUMP";   
  logicActivated = true;
  selectedLogic = 0;
 // selectedMode = 0;
 // selectedLogic = 0;
 commonstoptimer();
}

/*****************************************************************************************
           COMMON MANUAL MODE PUMP UTILITY OFF FUNCTION
 *****************************************************************************************/
void PUMPLOADOFF(){
  digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
  digitalWrite(DRIVES_PIN2_OUTPUT, LOW);
  delay(500);  
  digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
  digitalWrite(DRIVES_PIN2_OUTPUT, LOW);

     char USERMESSAGE[] = "MANUAL PUMP UTILITY OFF";
for (int i = 0; i < numAllowedNumbers; i++) {
  fona.sendSMS(allowedPhoneNumbers[i], USERMESSAGE);
}
  
  lcd.setCursor(0, 0);
  lcd.print("               ");
  //delay(500);
  lcd.setCursor(0, 0);
  lcd.print("MANUAL OFF");
  //delay(500);
  //SerialBT.print("MANUAL");
  Serial.println("PUMP UTILITY OFF");
  updateSMSStatus("PUMP UTILITY OFF");
  isAutoModeSolar = false;
  DRIVES_STATUS = 1;
  currentMode = "MANUAL PUMP UTILITY OFF";
  logicActivated = 0;

 // saveRemainingTime1(0, PUMP1_REMAINING_TIME_ADDRESS);
  //pump1Counter = 0;

  //logicActivated = true;
  //selectedLogic = 0;
  commonstoptimer();
}

/*****************************************************************************************
           COMMON MANUAL MODE UTILITY FUNCTION
 *****************************************************************************************/
void MANUALMODEUTILITY(){
  digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
  digitalWrite(DRIVES_PIN2_OUTPUT, LOW);
  delay(500);
  digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
  digitalWrite(DRIVES_PIN2_OUTPUT, HIGH);

    char USERMESSAGE[] = "MANUAL UTILITY ON";
for (int i = 0; i < numAllowedNumbers; i++) {
  fona.sendSMS(allowedPhoneNumbers[i], USERMESSAGE);
}
  
  lcd.setCursor(0, 0);
  lcd.print("               ");
  //delay(500);
  lcd.setCursor(0, 0);
  lcd.print("MANUAL ON");
  //delay(500);
  //SerialBT.print("MANUAL");
  Serial.println("MANUAL UTILITY");
  updateSMSStatus("MANUAL UTILITY");
  isAutoModeSolar = false;
  DRIVES_STATUS = 1;
  currentMode = "MANUAL UTILITY";   
  logicActivated = true;
  selectedLogic = 1;
 // selectedMode = 0;
 // selectedLogic = 0;
 commonstoptimer();
}


/*****************************************************************************************
           COMMON MANUAL MODE PUMP UTILITY FUNCTION
 *****************************************************************************************/
void MANUALMODEPUMPUTILITY(){
  digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
  digitalWrite(DRIVES_PIN2_OUTPUT, LOW);
  delay(500);

  digitalWrite(DRIVES_PIN1_OUTPUT, HIGH);
  digitalWrite(DRIVES_PIN2_OUTPUT, HIGH);

    char USERMESSAGE[] = "MANUAL PUMP UTILITY ON";
for (int i = 0; i < numAllowedNumbers; i++) {
  fona.sendSMS(allowedPhoneNumbers[i], USERMESSAGE);
}
  
  lcd.setCursor(0, 0);
  lcd.print("               ");
  //delay(500);
  lcd.setCursor(0, 0);
  lcd.print("MANUAL ON");
  //delay(500);
  //SerialBT.print("MANUAL");
  Serial.println("MANUAL PUMP UTILITY");
  updateSMSStatus("MANUAL PUMP UTILITY");
  isAutoModeSolar = false;
  DRIVES_STATUS = 1;
  currentMode = "MANUAL PUMP UTILITY";   
  logicActivated = true;
  selectedLogic = 2;
 // selectedMode = 0;
 // selectedLogic = 0;
 commonstoptimer();
}


/*****************************************************************************************
           COMMON AUTO MODE PUMP ON FUNCTION
 *****************************************************************************************/
void AUTOMODE(){
  //digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
  //digitalWrite(DRIVES_PIN2_OUTPUT, HIGH);
  //delay(2000);
  isAutoModeSolar = true;

char USERMESSAGE[] = "AUTO MODE ON";
for (int i = 0; i < numAllowedNumbers; i++) {
  fona.sendSMS(allowedPhoneNumbers[i], USERMESSAGE);
}

  lcd.setCursor(0, 0);
  lcd.print("               ");
  delay(500);
  lcd.setCursor(0, 0);
  lcd.print("AUTO ON");
  
  updateSMSStatus("AUTO MODE");
  DRIVES_STATUS = 1;
  currentMode = "AUTO MODE"; 

  logicActivated = true;
  selectedLogic = 3; 
  //selectedMode = 1;
  commonstoptimer();
     
}

/*****************************************************************************************
           COMMON AUTO MODE PUMP OFF FUNCTION
 *****************************************************************************************/
void AUTOMODEOFF(){
digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
  digitalWrite(DRIVES_PIN2_OUTPUT, LOW);
  delay(500); 
isAutoModeSolar = false;

digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
digitalWrite(DRIVES_PIN2_OUTPUT, LOW);

char USERMESSAGE[] = "AUTO MODE OFF";
for (int i = 0; i < numAllowedNumbers; i++) {
  fona.sendSMS(allowedPhoneNumbers[i], USERMESSAGE);
}

lcd.setCursor(0, 0);
lcd.print("               ");
delay(500);
lcd.setCursor(0, 0);
lcd.print("AUTO OFF");
delay(500);
//SerialBT.print("MANUAL");
Serial.println("AUTO MODE OFF");
updateSMSStatus("AUTO MODE OFF");

DRIVES_STATUS = 1;
currentMode = "AUTO MODE OFF";   

logicActivated = 0;

// saveRemainingTime1(0, PUMP1_REMAINING_TIME_ADDRESS);
//pump1Counter = 0;

//logicActivated = true;
//selectedLogic = 0;
commonstoptimer();
}

/*****************************************************************************************
           COMMON SENSOR OPERATION FUNCTION
 *****************************************************************************************/
void TOPTANK(){
  // Logic for automatic mode
        if (!isWaterPresent()) { 
            digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
            digitalWrite(DRIVES_PIN2_OUTPUT, LOW);
            delay(500);
            Serial.println("WATER FULL TANK");
            full = 1;
            pumping = 0;
            delay(500);
            
        }
        else if (!isWaterPresent2()) {  
            Serial.println("Waiting...");
           if(full == 1){
            Serial.println("TANK WATER IS GOING BELOW THE SENSOR 1");
           }
           else if(pumping == 1){
           Serial.println("WATER IS PUMPING UP TO TANK");
           }      
            delay(500);
        }        
        else {
            //digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
            //digitalWrite(DRIVES_PIN2_OUTPUT, HIGH);
            //delay(2000);
            digitalWrite(DRIVES_PIN1_OUTPUT, HIGH);
            digitalWrite(DRIVES_PIN2_OUTPUT, LOW);
            delay(500);
            Serial.println("WATER IS PUMPING UP TO TANK");
            full = 0;
            pumping = 1;
            delay(500);
            
        }
}

/*****************************************************************************************
           COMMON TIMER PUMP ON FUNCTION
 *****************************************************************************************/
void TIMERMODEPUMP(){
digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
  digitalWrite(DRIVES_PIN2_OUTPUT, LOW);
  delay(500);
  digitalWrite(DRIVES_PIN1_OUTPUT, HIGH);
  digitalWrite(DRIVES_PIN2_OUTPUT, LOW);
  
   char msg21[] = "TIMER PUMP ON";
for (int i = 0; i < numAllowedNumbers; i++) {
  fona.sendSMS(allowedPhoneNumbers[i], msg21);
}
  
  lcd.setCursor(0, 0);
  lcd.print("               ");
  delay(500);
  lcd.setCursor(0, 0);
  lcd.print("TIMER ON");
  delay(500);
  //SerialBT.print("MANUAL");
  Serial.println("TIMER PUMP");
  updateSMSStatus("TIMER PUMP");
  isAutoModeSolar = false;
  DRIVES_STATUS = 1;
  currentMode = "TIMER PUMP";   
  
  //logicActivated = true;
  //selectedLogic = 4;

  //selectedMode = 0;
  //selectedLogic = 0;

}

/*****************************************************************************************
           COMMON TIMER PUMP OFF FUNCTION
 *****************************************************************************************/
void TIMEROFF(){
  digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
  digitalWrite(DRIVES_PIN2_OUTPUT, LOW);
  delay(500);
  isAutoModeSolar = false;
  
  digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
  digitalWrite(DRIVES_PIN2_OUTPUT, LOW);

  char msg25[] = "TIMER PUMP OFF";
for (int i = 0; i < numAllowedNumbers; i++) {
  fona.sendSMS(allowedPhoneNumbers[i], msg25);
}
  
  lcd.setCursor(0, 0);
  lcd.print("               ");
  delay(500);
  lcd.setCursor(0, 0);
  lcd.print("TIMER OFF");
  delay(500);
  //SerialBT.print("MANUAL");
  Serial.println("TIMER OFF");
  updateSMSStatus("TIMER OFF");
  
  DRIVES_STATUS = 1;
  currentMode = "TIMER OFF";   
  

 // saveRemainingTime1(0, PUMP1_REMAINING_TIME_ADDRESS);
  //pump1Counter = 0;

  //logicActivated = true;
  //selectedLogic = 4;

}

/*****************************************************************************************
           COMMON TIMER MODE PUMP OFF FUNCTION
 *****************************************************************************************/
void TIMERMODEOFF(){
  digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
  digitalWrite(DRIVES_PIN2_OUTPUT, LOW);
  delay(500);

digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
digitalWrite(DRIVES_PIN2_OUTPUT, LOW);

  char msg21[] = "TIMER MODE OFF";
for (int i = 0; i < numAllowedNumbers; i++) {
  fona.sendSMS(allowedPhoneNumbers[i], msg21);
}

lcd.setCursor(0, 0);
lcd.print("               ");
delay(500);
lcd.setCursor(0, 0);
lcd.print("TIMER MODE OFF");
delay(500);
//SerialBT.print("MANUAL");
Serial.println("TIMER MODE OFF");
updateSMSStatus("TIMER MODE OFF");
isAutoModeSolar = false;

DRIVES_STATUS = 1;
currentMode = "TIMER MODE OFF";   


// saveRemainingTime1(0, PUMP1_REMAINING_TIME_ADDRESS);
//pump1Counter = 0;

//logicActivated = true;
//selectedLogic = 0;

}

/*****************************************************************************************
           COMMON TIMER STOP FUNCTION FOR PUMP1
 *****************************************************************************************/
void STOPPUMP1()
{ 

  digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
  digitalWrite(DRIVES_PIN2_OUTPUT, LOW);
  delay(500);
  digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
  digitalWrite(DRIVES_PIN2_OUTPUT, LOW);

  char USERMESSAGE[] = "TIMER PUMP OFF";
for (int i = 0; i < numAllowedNumbers; i++) {
  fona.sendSMS(allowedPhoneNumbers[i], USERMESSAGE);
}
           
  lcd.setCursor(0, 0);
  lcd.print("               ");
  delay(500);
  lcd.setCursor(0, 0);
  lcd.print("STOP PUMP");
  delay(500);
  //SerialBT.print("MANUAL");
  Serial.println("STOP PUMP");
  updateSMSStatus("STOP PUMP");

  //SPI.begin();
  //digitalWrite(CS_1, LOW);
  saveRemainingTime1(0, PUMP1_REMAINING_TIME_ADDRESS);
  pump1Counter = 0;
  //digitalWrite(CS_1, HIGH);
  //SPI.end();
 // LOADOFF();
 //stoptimermode = 0;

  isAutoModeSolar = false;
  DRIVES_STATUS = 1;
  currentMode = "STOP PUMP";

}
/*****************************************************************************************
           COMMON TIMER STOP FUNCTION FOR BPUMP
 *****************************************************************************************/
void BSTOPPUMP1()
{ 

  digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
  digitalWrite(DRIVES_PIN2_OUTPUT, LOW);
  delay(500);
  digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
  digitalWrite(DRIVES_PIN2_OUTPUT, LOW);

   char USERMESSAGE[] = "TIMER PUMP OFF";
for (int i = 0; i < numAllowedNumbers; i++) {
  fona.sendSMS(allowedPhoneNumbers[i], USERMESSAGE);
}
            
  lcd.setCursor(0, 0);
  lcd.print("               ");
  delay(500);
  lcd.setCursor(0, 0);
  lcd.print("STOP BPUMP");
  delay(500);
  //SerialBT.print("MANUAL");
  Serial.println("STOP BPUMP");
  updateSMSStatus("STOP BPUMP");

 // SPI.begin();
//  digitalWrite(CS_1, LOW);
  BsaveRemainingTime1(0, BPUMP1_REMAINING_TIME_ADDRESS);
  Bpump1Counter = 0;
//  digitalWrite(CS_1, HIGH);
//  SPI.end();
 // LOADOFF();
 //stoptimermode = 0;
 //logicActivated = true;
   // selectedLogic = 5;

  isAutoModeSolar = false;
  DRIVES_STATUS = 1;
  currentMode = "STOP BPUMP";

}

/*****************************************************************************************
           COMMON TIMER STOP FUNCTION FOR CPUMP
 *****************************************************************************************/
void CSTOPPUMP1()
{ 

  digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
  digitalWrite(DRIVES_PIN2_OUTPUT, LOW);
  delay(500);
  digitalWrite(DRIVES_PIN1_OUTPUT, LOW);
  digitalWrite(DRIVES_PIN2_OUTPUT, LOW);

   char USERMESSAGE[] = "TIMER PUMP OFF";
for (int i = 0; i < numAllowedNumbers; i++) {
  fona.sendSMS(allowedPhoneNumbers[i], USERMESSAGE);
}
            
  lcd.setCursor(0, 0);
  lcd.print("               ");
  delay(500);
  lcd.setCursor(0, 0);
  lcd.print("STOP CPUMP");
  delay(500);
  //SerialBT.print("MANUAL");
  Serial.println("STOP CPUMP");
  updateSMSStatus("STOP CPUMP");

  CsaveRemainingTime1(0, CPUMP1_REMAINING_TIME_ADDRESS);
  Cpump1Counter = 0;

 //stoptimermode = 0;

 //logicActivated = true;
 //selectedLogic = 6;

  isAutoModeSolar = false;
  DRIVES_STATUS = 1;
  currentMode = "STOP CPUMP";

}


 /*****************************************************************************************
           COMMON STOP TIMER MODE
 *****************************************************************************************/
void stoptimermode()
{ 
  SPI.begin();
  digitalWrite(CS_1, LOW);
  flash.eraseSector(PUMP1_DATA_ADDR);
  flash.eraseSector(PUMP1_REMAINING_TIME_ADDRESS);
  saveRemainingTime1(0, PUMP1_REMAINING_TIME_ADDRESS);
  pump1Counter = 0;
  pump1DurationMinutes = 0;
  storePump1Data(pump1StartHour = 25, pump1StartMinute = 0, pump1DurationMinutes = 0, pump1RemainingTime = 0);
  ////////////////////////2ND TIMER/////////////////////
  flash.eraseSector(BPUMP1_DATA_ADDR);
  flash.eraseSector(BPUMP1_REMAINING_TIME_ADDRESS);
  BsaveRemainingTime1(0, BPUMP1_REMAINING_TIME_ADDRESS);
  Bpump1Counter = 0;
  Bpump1DurationMinutes = 0;
  BstorePump1Data(Bpump1StartHour = 25, Bpump1StartMinute = 0, Bpump1DurationMinutes = 0, Bpump1RemainingTime = 0);
  ///////////////////////3RD TIMER//////////////////////
  flash.eraseSector(CPUMP1_DATA_ADDR);
  flash.eraseSector(CPUMP1_REMAINING_TIME_ADDRESS);
  CsaveRemainingTime1(0, CPUMP1_REMAINING_TIME_ADDRESS);
  Cpump1Counter = 0;
  Cpump1DurationMinutes = 0;
  CstorePump1Data(Cpump1StartHour = 25, Cpump1StartMinute = 0, Cpump1DurationMinutes = 0, Cpump1RemainingTime = 0);

  digitalWrite(CS_1, HIGH);
  SPI.end();
  TIMERMODEOFF();
  pump1MissedSent = true;
  savePump1MissedFlag(true);
  Bpump1MissedSent = true;
  saveBPumpMissedFlag(true);
  Cpump1MissedSent = true;
  saveCPumpMissedFlag(true);
  //stoptimermode = 1;
  isAutoModeSolar = false;
  DRIVES_STATUS = 1;
  currentMode = "STOP TIMER";
}

/*****************************************************************************************
           COMMON CHANGE OVER MODE'S, STOP'S THE TIMER
 *****************************************************************************************/
void commonstoptimer()
{ 
  SPI.begin();
  digitalWrite(CS_1, LOW);
  flash.eraseSector(PUMP1_DATA_ADDR);
  flash.eraseSector(PUMP1_REMAINING_TIME_ADDRESS);
  saveRemainingTime1(0, PUMP1_REMAINING_TIME_ADDRESS);
  pump1Counter = 0;
  pump1DurationMinutes = 0;
  storePump1Data(pump1StartHour = 25, pump1StartMinute = 0, pump1DurationMinutes = 0, pump1RemainingTime = 0);
  ///////////////////////////2ND TIMER/////////////////////////
  flash.eraseSector(BPUMP1_DATA_ADDR);
  flash.eraseSector(BPUMP1_REMAINING_TIME_ADDRESS);
  BsaveRemainingTime1(0, BPUMP1_REMAINING_TIME_ADDRESS);
  Bpump1Counter = 0;
  Bpump1DurationMinutes = 0;
  BstorePump1Data(Bpump1StartHour = 25, Bpump1StartMinute = 0, Bpump1DurationMinutes = 0, Bpump1RemainingTime = 0);
  //////////////////////////3RD TIMER////////////////////////
   flash.eraseSector(CPUMP1_DATA_ADDR);
  flash.eraseSector(CPUMP1_REMAINING_TIME_ADDRESS);
  CsaveRemainingTime1(0, CPUMP1_REMAINING_TIME_ADDRESS);
  Cpump1Counter = 0;
  Cpump1DurationMinutes = 0;
  CstorePump1Data(Cpump1StartHour = 25, Cpump1StartMinute = 0, Cpump1DurationMinutes = 0, Cpump1RemainingTime = 0);

  digitalWrite(CS_1, HIGH);
  SPI.end(); 
}

/*****************************************************************************************
           STORE WIFI USER ID UPDATED FUNCTION
 *****************************************************************************************/
void updateSSID(const char *newSSID) {
  SPI.begin();
  uint32_t ssidAddress = SSID_ADDRESS;
  digitalWrite(CS_1, LOW);
  flash.eraseSector(ssidAddress);
  for (int i = 0; i < strlen(newSSID); i++) {
    flash.writeByte(ssidAddress + i, newSSID[i]);
  }
  flash.writeByte(ssidAddress + strlen(newSSID), '\0');
  digitalWrite(CS_1, HIGH);
  Serial.println("Updated SSID in Flash:");
  Serial.println(newSSID);
  SPI.end();
}

/*****************************************************************************************
           STORE WIFI USER PASSWORD UPDATED FUNCTION
 *****************************************************************************************/
void updatePassword(const char *newPassword) {
  SPI.begin();
  uint32_t passwordAddress = PASSWORD_ADDRESS;
  digitalWrite(CS_1, LOW);
  flash.eraseSector(passwordAddress);
  for (int i = 0; i < strlen(newPassword); i++) {
    flash.writeByte(passwordAddress + i, newPassword[i]);
  }
  flash.writeByte(passwordAddress + strlen(newPassword), '\0');
  digitalWrite(CS_1, HIGH);
  Serial.println("Updated Password in Flash:");
  Serial.println(newPassword);
  SPI.end();
}

/*****************************************************************************************
           RETRIVE WIFI USER ID UPDATED FUNCTION
 *****************************************************************************************/
void loadSSID() {
  SPI.begin();
  uint32_t ssidAddress = SSID_ADDRESS;
  digitalWrite(CS_1, LOW);
  for (int i = 0; i < sizeof(wifi_ssid); i++) {
    wifi_ssid[i] = flash.readByte(ssidAddress + i);
    if (wifi_ssid[i] == '\0') break;
  }
  digitalWrite(CS_1, HIGH);
  wifi_ssid[sizeof(wifi_ssid) - 1] = '\0';
  Serial.println("Loaded SSID from Flash:");
  Serial.println(wifi_ssid);
  SPI.end();
}

/*****************************************************************************************
           RETRIVE WIFI USER PASSWORD UPDATED FUNCTION
 *****************************************************************************************/
void loadPassword() {
  SPI.begin();
  uint32_t passwordAddress = PASSWORD_ADDRESS;
  digitalWrite(CS_1, LOW);
  for (int i = 0; i < sizeof(wifi_password); i++) {
    wifi_password[i] = flash.readByte(passwordAddress + i);
    if (wifi_password[i] == '\0') break;
  }
  digitalWrite(CS_1, HIGH);
  wifi_password[sizeof(wifi_password) - 1] = '\0';
  Serial.println("Loaded Password from Flash:");
  Serial.println(wifi_password);
  SPI.end();
}

/*****************************************************************************************
           RECONNECTING TO MQTT
 *****************************************************************************************/

void reconnect() {

  //  WiFi must be ready
  if (WiFi.status() != WL_CONNECTED) {
    Serial.println("WiFi not connected — MQTT skipped");
    return;
  }

  if (WiFi.localIP() == IPAddress(0, 0, 0, 0)) {
  Serial.println("IP not ready — MQTT skipped");
  return;
}


/////////////////
  Serial.println("Attempting MQTT connection...");
  delay(500); // IMPORTANT (do not remove)

  // Your same connect function
  if (client.connect(
            mqtt_clientId,
            mqtt_username,
            mqtt_password,
            "hical/data2",
            1,
            true,
            "DISCONNECTED",
            true
        ))
  {
    Serial.println("MQTT connected!");
          /*for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], "MQTT CONNECTED");
          }*/
         char smsMsg[] = "MQTT CONNECTED";
         for (int i = 0; i < numAllowedNumbers; i++) {
         fona.sendSMS(allowedPhoneNumbers[i], smsMsg);
         }

    client.publish("hical/data2", "CONNECTED", true);
    BWS = "WIFI";    // current mode you want to store
   updateBWSStatus(BWS.c_str());  // <--- STORE to flash
   linkswitches = 0;
    client.subscribe("hical/2");
  } 
  else 
  {
    Serial.print("failed, rc=");
    Serial.println(client.state());
  }
}

/*****************************************************************************************
           RECEIVING THE DATA OF MQTT
 *****************************************************************************************/
void callback(char* topic, byte* payload, unsigned int length) {
  Serial.print("Message arrived on topic: ");
  Serial.print(topic);
  Serial.print(". Message: ");
  String mqttmessage;

  for (int i = 0; i < length; i++) {
    mqttmessage += (char)payload[i];
  }
  Serial.println(mqttmessage);

     BWS = "WIFI";    // current mode you want to store
   updateBWSStatus(BWS.c_str());  // <--- STORE to flash
   linkswitches = 0;

  // Handle incoming MQTT messages if needed
  if (mqttmessage == "MANUAL PUMP") { MANUALMODEPUMP(); }
  else if (mqttmessage == "PUMP UTILITY OFF") { PUMPLOADOFF();  }
  else if (mqttmessage == "MANUAL UTILITY") { MANUALMODEUTILITY(); }
  else if (mqttmessage == "MANUAL PUMP UTILITY") { MANUALMODEPUMPUTILITY(); }
  else if (mqttmessage == "AUTO MODE") { AUTOMODE(); }
  else if (mqttmessage == "AUTO MODE OFF") { AUTOMODEOFF();  }
  else if (mqttmessage.startsWith("PUMP:")) { updatePumpSchedule(mqttmessage);
    delay(200);
    pump1MissedSent = false; 
    savePump1MissedFlag(false); }
  else if (mqttmessage.startsWith("BPUMP:")) { BupdatePumpSchedule(mqttmessage);
    delay(200);
    Bpump1MissedSent = false; 
    saveBPumpMissedFlag(false); }
  else if (mqttmessage.startsWith("CPUMP:")) { CupdatePumpSchedule(mqttmessage); 
    delay(200);
    Cpump1MissedSent = false; 
    saveCPumpMissedFlag(false); }
  else if (mqttmessage.startsWith("STOP PUMP")) { STOPPUMP1(); }
  else if (mqttmessage.startsWith("STOP BPUMP")) { BSTOPPUMP1(); }
  else if (mqttmessage.startsWith("STOP CPUMP")) { CSTOPPUMP1(); }
  else if (mqttmessage.startsWith("STOP TIMER")) { stoptimermode(); }
  else if (mqttmessage == "keyactive") { 
     DRIVES_STATUS = 1;
    switchcontrolvar = 1;
    currentMode = "keyactive";
    storeSwitchControlVar(switchcontrolvar);
    }
  else if (mqttmessage == "keydeactive") { 
    DRIVES_STATUS = 1;
    switchcontrolvar = 0;
    currentMode = "keydeactive";
    storeSwitchControlVar(switchcontrolvar);
    }   

 ///////    
   else if (mqttmessage.startsWith("E")) { // Update SSID in a single step
    String newSSID = mqttmessage.substring(1); // Extract the part after "E"
    newSSID.trim(); // Remove unnecessary spaces or newline characters

    if (newSSID.length() > 0) {
        updateSSID(newSSID.c_str()); // Update SSID
        WiFi.begin(newSSID.c_str(), wifi_password); // Reconnect WiFi with updated SSID
        Serial.println("SSID updated successfully to: ");
    } else {
        Serial.println("Invalid SSID. Please provide a valid one.");
    }
    loadSSID(); //RETRIVE SSID OF WIFI
  
} 
else if (mqttmessage.startsWith("F")) { // Update WiFi Password in a single step
    String newPassword = mqttmessage.substring(1); // Extract the part after "F"
    newPassword.trim(); // Remove unnecessary spaces or newline characters

    if (newPassword.length() > 0) {
        updatePassword(newPassword.c_str()); // Update password
        WiFi.begin(wifi_ssid, newPassword.c_str()); // Reconnect WiFi with updated password
        Serial.println("WiFi password updated successfully.");
    } else {
        Serial.println("Invalid password. Please provide a valid one.");
    }
    loadPassword(); //RETRIVE PASSWORD OF WIFI
} 

// SIMCARD AND GPS UNPLUG PASSWORD
   else if (mqttmessage.startsWith("H")) { // Command to set the password via Bluetooth
    String newPassword = mqttmessage.substring(1); // Extract the part after "H"
    newPassword.trim(); // Remove any unwanted spaces or newline characters

    // Check if the new password is valid (e.g., 4 digits)
    if (newPassword.length() == 4 && newPassword.toInt() != 0) {
        password = newPassword; // Update the password
        storelockPasswordInFlash(password); // Store the new password in flash memory
        Serial.println("Password updated to: " + password);
    } else {
        Serial.println("Invalid password format. Please use a 4-digit password.");
    }
}
////////
 else if (mqttmessage == "GET LOCATION") {
    sendLocationToUsers();   // SMS only
}

else if (mqttmessage == "INITIAL SEARCH") 
  { 
    if(isLocked == true){
    currentStatusMessageSMS = "searching.";
  }
  else{
    currentStatusMessageSMS = "Searching";
  }
  }
  else if(mqttmessage == "YES")
    {
       isLocked = true;  // Lock the system
       storeLockStatus(isLocked);
       smstimer = 0;
       gpstimer = 0;
    }

    else if(mqttmessage == "NO")
    {
      isLocked = false;  // Lock the system
       storeLockStatus(isLocked);
        DRIVES_STATUS = 1;
        smstimer = 1;
       gpstimer = 1;
    }

    else if(mqttmessage == "UNLOCK")
    {
       isLocked = false;  // Lock the system
       storeLockStatus(isLocked);
        float currentLatitude, currentLongitude;
                if (fona.getGPS(&currentLatitude, &currentLongitude)) {
                    char fullLatitude[15];  // Buffer for full latitude
                    char fullLongitude[15]; // Buffer for full longitude

                    // No significant location change, continue normal operation
                    snprintf(fullLatitude, sizeof(fullLatitude), "%.6f", currentLatitude);
                    snprintf(fullLongitude, sizeof(fullLongitude), "%.6f", currentLongitude);
                    char locationMsg[100];
                    delay(1000);
                    snprintf(locationMsg, sizeof(locationMsg), "Click the link to view the location: https://maps.google.com/?q=%.6f,%.6f", currentLatitude, currentLongitude);

                    // Send SMS to all allowed numbers
                    for (int i = 0; i < numAllowedNumbers; i++) {
                        fona.sendSMS(allowedPhoneNumbers[i], locationMsg);
                    }

                    // Optionally update previous coordinates
                    previousLatitude = currentLatitude;
                    previousLongitude = currentLongitude;
                    storePreviousLocation(previousLatitude, previousLongitude);
                }
       DRIVES_STATUS = 1;
       loadupdatedSMSStatus();
       Previousstate();
       smstimer = 1;
       gpstimer = 1;
       signal();
    }
   
}

/*****************************************************************************************
           MQTT DATA PUBLISH FROM BOARD
 *****************************************************************************************/
void publishStatusNow() {
  DynamicJsonDocument doc(capacity);
  doc["status"] = currentStatusMessageSMS;
  doc["Remaining"] = pump1Counter;
  doc["BRemaining"] = Bpump1Counter;
  doc["CRemaining"] = Cpump1Counter;
  doc["KEY1"] = switchcontrolvar;
  doc["Wifi"] = WiFi.status() == WL_CONNECTED ? "Connected" : "Disconnected";
  doc["wifi_ssid"] = WiFi.SSID();
  doc["wifi_password"] = wifi_password;
  doc["Bluetooth"] = isConnected ? "Connected" : "Disconnected";
  doc["Operatedmode"] = currentMode;
  doc["linkswitches"] = linkswitches;  

  String jsonString;
  serializeJsonPretty(doc, jsonString);

  client.publish("hical/data2", jsonString.c_str());
  Serial.println("Published status immediately.");
}

/*****************************************************************************************
           LOCATION TRACKING FUNCTION
 *****************************************************************************************/
void gps(){
    /////////LOCATION START//////////
   char callerIDbuffer[32]; // we'll store the SMS sender number in here
  
   // Check for GPS status and read the current location
    if (fona.GPSstatus() == 0) {
        //fona.sendSMS(callerIDbuffer, "GPS not locked. Please wait and try again.");
        char msg18[] =  "GPS not locked. Please wait and try again.";
        fona.sendSMS(callerIDbuffer, msg18);
         
    } else {
     
        float currentLatitude, currentLongitude;
        if (fona.getGPS(&currentLatitude, &currentLongitude)) {
  
  
          // Reset failure counter on successful location retrieval
            failureCounter = 0;
            updateFailureCounter(failureCounter);
            Serial.println("Failure Counter: 0");
          
            // Call the function to check location changes and send SMS
            checkLocationAndSendSMS(callerIDbuffer, currentLatitude, currentLongitude);
        }else {
            smstimer = 0;
            gpstimer = 0;
           char GPS[] = "NO GPS SIGNAL, Do You Want to Lock the System YES/NO";
        for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], GPS);
        }
        delay(500);
        currentStatusMessageSMS =  "NO GPS SIGNAL, Do You Want to Lock the System YES/NO";
        SerialBT.println(String(currentStatusMessageSMS) + "|" + pump1Counter + "|" + Bpump1Counter + "|" + Cpump1Counter + "|" + switchcontrolvar + "|" + linkswitches);
        delay(500);
        publishStatusNow();
        
           // Increment failure counter on failure
            failureCounter++;
            updateFailureCounter(failureCounter);
            Serial.print("Failure Counter: ");
            Serial.println(failureCounter);
          
        /*for (int i = 0; i < numAllowedNumbers; i++) {
            //fona.sendSMS(allowedPhoneNumbers[i], "Failed to retrieve location.");
            //char msg19[] =  "Failed to retrieve location.";
           //fona.sendSMS(allowedPhoneNumbers[i], msg19);
        }*/
       
          // Check and handle lock status
            checkAndHandleLockStatus();
            //fona.sendSMS(callerIDbuffer, "Failed to retrieve location.");
        }
  } 
  ////////LOCATION END//////////////
}

/*****************************************************************************************
           CHECKS THE LOCATION AND SEND A SMS TO USER LOCKED OR NOT
 *****************************************************************************************/
// Function to check for location changes and send SMS if the system isn't locked
void checkLocationAndSendSMS(char* callerIDbuffer, float currentLatitude, float currentLongitude) {
   
   loadPreviousLocation(&previousLatitude, &previousLongitude);
    if (isLocked) {
        //fona.sendSMS(callerIDbuffer, "System is locked. Only location tracking is allowed.");
        char msg20[] =  "System is locked.";
           fona.sendSMS(callerIDbuffer, msg20);
        
        return;
    }

    // Check for valid previous coordinates
    if (isnan(previousLatitude) || isnan(previousLongitude)) {
        // If previous coordinates are invalid, update them with the current values
        previousLatitude = currentLatitude;
        previousLongitude = currentLongitude;
        storePreviousLocation(previousLatitude, previousLongitude);
        return; // Exit the function after storing the new location
    }

    // Calculate the distance between previous and current coordinates
    float distance = haversine(previousLatitude, previousLongitude, currentLatitude, currentLongitude);
    Serial.print("Distance: ");
    Serial.println(distance);
    
    // If the distance is greater than or equal to 1 km (1.0), lock the system
    if (distance >= Setdistance) //E.g 0.5 500METERS 
    {    smstimer = 0;
        gpstimer = 0;
         char GPS[] = "SET LOCATION HAS SHIFTED, Do You Want to Lock the System YES/NO";
        for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], GPS);
        }
        delay(500);

        currentStatusMessageSMS = "SET LOCATION HAS SHIFTED, Do You Want to Lock the System YES/NO";
        SerialBT.println(String(currentStatusMessageSMS) + "|" + pump1Counter + "|" + Bpump1Counter + "|" + Cpump1Counter + "|" + switchcontrolvar + "|" + linkswitches);
       delay(500);

       publishStatusNow();
        
        isLocked = true;  // Lock the system
        storeLockStatus(isLocked);  // Save the updated lock status
        //fona.sendSMS(callerIDbuffer, "Location changed by 1km. System is now locked.");
        // You can add logic here to handle the lock (e.g., disable certain functions)
         char fullLatitude[15];  // Buffer for full latitude
        char fullLongitude[15]; // Buffer for full longitude

        // No significant location change, continue normal operation
        snprintf(fullLatitude, sizeof(fullLatitude), "%.6f", currentLatitude);
        snprintf(fullLongitude, sizeof(fullLongitude), "%.6f", currentLongitude);
        char locationMsg[100];
        //delay(2000);
        snprintf(locationMsg, sizeof(locationMsg), "Click the link to view the location: https://maps.google.com/?q=%.6f,%.6f", currentLatitude, currentLongitude);
         // Send SMS to all allowed numbers
        for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], locationMsg);  
        }

    } else {
      
         char GPS[] = "PRESENT LOCATION MATCHED, DRIVES WILL RUN NORMALLY";
        for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], GPS);
        }
        delay(500);

        currentStatusMessageSMS =  "PRESENT LOCATION MATCHED, DRIVES WILL RUN NORMALLY";
        SerialBT.println(String(currentStatusMessageSMS) + "|" + pump1Counter + "|" + Bpump1Counter + "|" + Cpump1Counter + "|" + switchcontrolvar + "|" + linkswitches);
        delay(500);
        publishStatusNow();
         
         //loadupdatedSMSStatus();
         //Previousstate();
         smstimer = 1;
         gpstimer = 1;
          // Format latitude and longitude for sending to the user
        char fullLatitude[15];  // Buffer for full latitude
        char fullLongitude[15]; // Buffer for full longitude

        // No significant location change, continue normal operation
        snprintf(fullLatitude, sizeof(fullLatitude), "%.6f", currentLatitude);
        snprintf(fullLongitude, sizeof(fullLongitude), "%.6f", currentLongitude);
        char locationMsg[100];
        delay(1000);
        snprintf(locationMsg, sizeof(locationMsg), "Click the link to view the location: https://maps.google.com/?q=%.6f,%.6f", currentLatitude, currentLongitude);
         // Send SMS to all allowed numbers
        for (int i = 0; i < numAllowedNumbers; i++) {
            //fona.sendSMS(allowedPhoneNumbers[i], locationMsg);
            
        }
    }
}

/*****************************************************************************************
           PASSWORD UNLOCK SWITCH FUNCTION
 *****************************************************************************************/
void handleSwitchInput(int switchState1, int switchState2) {
    static unsigned long pressStartTime = 0; // Tracks the start time of the press
    static bool isLongPress = false;         // Tracks if a long press occurred
    
    if (isLocked) {
        // Handle Switch 1 (Short press to increment digit, long press to move to next digit)
        if (switchState1 == LOW) {
            if (pressStartTime == 0) {
                pressStartTime = millis();  // Start tracking press duration
            }

            // Check if it's a long press (hold for more than 1 second)
            if (millis() - pressStartTime > 300 && !isLongPress) {
                isLongPress = true;        // Mark as long press
                currentDigit = (currentDigit + 1) % 4;  // Move to the next digit
                underscoreVisible = true; // Show underscore when moving to a new digit
                pressStartTime = 0;       // Reset press time
                delay(300);               // Debounce
            }
        } else {
            if (!isLongPress && pressStartTime != 0) {
                // Short press logic: Increment the current digit
                inputPassword[currentDigit] = (inputPassword[currentDigit] - '0' + 1) % 10 + '0'; // Increment digit
                underscoreVisible = false; // Hide underscore when digit is incremented
                delay(300);                // Debounce
            }
            // Reset for the next press
            isLongPress = false;
            pressStartTime = 0;
        }

        // Handle Switch 2 (Submit password)
        if (switchState2 == LOW) {
            if (inputPassword.equals(password)) {
                isLocked = false; // Unlock system if password is correct
                storeLockStatus(isLocked);  // Save the updated lock status
                lcd.clear();
                lcd.setCursor(0, 0);
                lcd.print("Password Correct!");
                Serial.println("Password Correct! System Unlocked.");
                delay(1000);
                inputPassword = "0000"; // Reset input for next use
                lcd.clear();

                // Reset failure counter on successful location retrieval
                failureCounter = 0;
                updateFailureCounter(failureCounter);

                // Handle GPS location and SMS logic
                float currentLatitude, currentLongitude;
                if (fona.getGPS(&currentLatitude, &currentLongitude)) {
                    char fullLatitude[15];  // Buffer for full latitude
                    char fullLongitude[15]; // Buffer for full longitude

                    // No significant location change, continue normal operation
                    snprintf(fullLatitude, sizeof(fullLatitude), "%.6f", currentLatitude);
                    snprintf(fullLongitude, sizeof(fullLongitude), "%.6f", currentLongitude);
                    char locationMsg[100];
                    delay(1000);
                    snprintf(locationMsg, sizeof(locationMsg), "Click the link to view the location: https://maps.google.com/?q=%.6f,%.6f", currentLatitude, currentLongitude);

                    // Send SMS to all allowed numbers
                    for (int i = 0; i < numAllowedNumbers; i++) {
                        fona.sendSMS(allowedPhoneNumbers[i], locationMsg);
                    }

                    // Optionally update previous coordinates
                    previousLatitude = currentLatitude;
                    previousLongitude = currentLongitude;
                    storePreviousLocation(previousLatitude, previousLongitude);
                }
                loadupdatedSMSStatus();
                Previousstate();
                smstimer = 1;
                gpstimer = 1;
                delay(500);
                //ESP.restart();
                return;  // Exit the function to avoid further password-related display
            } else {
                lcd.clear();
                lcd.setCursor(0, 0);
                lcd.print("Incorrect Password");
                Serial.println("Incorrect Password! Try again.");
                delay(1000); // Show incorrect message for 1 second
                inputPassword = "0000"; // Reset input on incorrect password
                lcd.clear();
            }
            delay(500); // Debounce
        }

        // Show password input progress on LCD
        lcd.clear();
        lcd.setCursor(0, 0);
        lcd.print("Password: ");

        // Display the current input password with a blinking underscore
        for (int i = 0; i < 4; i++) {
            if (i == currentDigit) {
                if (underscoreVisible) {
                    lcd.print('_'); // Show underscore for the current digit
                } else {
                    lcd.print(inputPassword[i]); // Hide underscore and show the actual digit
                }
            } else {
                lcd.print(inputPassword[i]); // Show other digits normally
            }
        }

        // Display the current digit position
        lcd.setCursor(0, 1);
        lcd.print("Digit: ");
        lcd.print(currentDigit + 1); // Show which digit user is editing (1-4)
    }
}

/*****************************************************************************************
           CALCULATION OF LOCATION DISTANCE
 *****************************************************************************************/
// Function to calculate the Haversine distance between two coordinates
float haversine(float lat1, float lon1, float lat2, float lon2) {
    float dLat = radians(lat2 - lat1);
    float dLon = radians(lon2 - lon1);
    lat1 = radians(lat1);
    lat2 = radians(lat2);

    float a = sin(dLat / 2) * sin(dLat / 2) +
              cos(lat1) * cos(lat2) * sin(dLon / 2) * sin(dLon / 2);
    float c = 2 * atan2(sqrt(a), sqrt(1 - a));

    return R * c;  // Distance in kilometers
}

/*****************************************************************************************
           STORE LOCATION
 *****************************************************************************************/
void storePreviousLocation(float previousLatitude, float previousLongitude) {
  SPI.begin();
  uint32_t locationAddress = LOCATION_ADDRESS;

  // Convert the float values to byte arrays
  byte latitudeBytes[sizeof(float)];
  byte longitudeBytes[sizeof(float)];

  memcpy(latitudeBytes, &previousLatitude, sizeof(float));
  memcpy(longitudeBytes, &previousLongitude, sizeof(float));

  // Erase the sector where the location will be stored
  digitalWrite(CS_1, LOW);
  flash.eraseSector(locationAddress);

  // Write the latitude bytes to flash memory
  for (int i = 0; i < sizeof(float); i++) {
    flash.writeByte(locationAddress + i, latitudeBytes[i]);
  }

  // Write the longitude bytes to flash memory right after the latitude
  for (int i = 0; i < sizeof(float); i++) {
    flash.writeByte(locationAddress + sizeof(float) + i, longitudeBytes[i]);
  }

  digitalWrite(CS_1, HIGH);
  Serial.println("Stored previous location in Flash:");
  Serial.print("Latitude: "); Serial.println(previousLatitude, 6);
  Serial.print("Longitude: "); Serial.println(previousLongitude, 6);
  SPI.end();
}

/*****************************************************************************************
           RETRIVE LOCATION
 *****************************************************************************************/
void loadPreviousLocation(float *previousLatitude, float *previousLongitude) {
  SPI.begin();
  digitalWrite(CS_1, LOW);
  uint32_t locationAddress = LOCATION_ADDRESS;

  // Buffers to hold the latitude and longitude bytes
  byte latitudeBytes[sizeof(float)];
  byte longitudeBytes[sizeof(float)];

  // Read the latitude bytes from flash memory
  for (int i = 0; i < sizeof(float); i++) {
    latitudeBytes[i] = flash.readByte(locationAddress + i);
  }

  // Read the longitude bytes from flash memory
  for (int i = 0; i < sizeof(float); i++) {
    longitudeBytes[i] = flash.readByte(locationAddress + sizeof(float) + i);
  }

  digitalWrite(CS_1, HIGH);

  // Convert the byte arrays back to float values
  memcpy(previousLatitude, latitudeBytes, sizeof(float));
  memcpy(previousLongitude, longitudeBytes, sizeof(float));

  Serial.println("Loaded previous location from Flash:");
  Serial.print("Latitude: "); Serial.println(*previousLatitude, 6);
  Serial.print("Longitude: "); Serial.println(*previousLongitude, 6);
  SPI.end();
}

/*****************************************************************************************
           STORE GPS FAILURE COUNTER
 *****************************************************************************************/
// Function to update failure counter in flash memory
void updateFailureCounter(int failureCounter) {
    SPI.begin();
    uint32_t address = FAILURE_COUNTER_ADDRESS;
    digitalWrite(CS_1, LOW);

    // Erase sector before writing
    flash.eraseSector(address);

    // Write failureCounter (2 bytes)
    flash.writeByte(address, (failureCounter >> 8) & 0xFF); // High byte
    flash.writeByte(address + 1, failureCounter & 0xFF);    // Low byte

    digitalWrite(CS_1, HIGH);
    SPI.end();
    Serial.println("Failure counter updated in flash.");
}

/*****************************************************************************************
        RETRIVE GPS FAILURE COUNTER    
 *****************************************************************************************/
// Function to load failure counter from flash memory
void loadFailureCounter(int &failureCounter) {
    SPI.begin();
    uint32_t address = FAILURE_COUNTER_ADDRESS;
    digitalWrite(CS_1, LOW);

    // Read failureCounter (2 bytes)
    failureCounter = (flash.readByte(address) << 8) | flash.readByte(address + 1);

    digitalWrite(CS_1, HIGH);
    SPI.end();
    //Serial.println("Failure counter loaded from flash.");
    //Serial.print("Failure Counter: ");
    //Serial.println(failureCounter);
}

/*****************************************************************************************
         COMPARING THE FAILURE COUNT AND SET COUNTER  
 *****************************************************************************************/
// Function to check and handle lock status
void checkAndHandleLockStatus() {
    if (failureCounter >= LOCK_THRESHOLD) {
        isLocked = true;
        storeLockStatus(isLocked); // Store lock status in flash memory
        Serial.println("Board locked due to excessive GPS failures.");
    }
}

/*****************************************************************************************
           STORE THE USER DEFINED SYSTEM LOCK PASSWORD
 *****************************************************************************************/
void storelockPasswordInFlash(const String& password) {
  SPI.begin();
  delay(100);
    digitalWrite(CS_1, LOW);  // Select the flash memory (CS low)
    
    flash.eraseSector(LOCKPASSWORD_ADDRESS); // Erase the sector where the password will be stored
    
    for (int i = 0; i < password.length(); i++) {
        flash.writeByte(LOCKPASSWORD_ADDRESS + i, password[i]); // Write each character to flash memory
    }
    
    // Write a null terminator to indicate the end of the password
    flash.writeByte(LOCKPASSWORD_ADDRESS + password.length(), '\0');
    
    Serial.print("Stored lock password: "); Serial.println(password);
    
    digitalWrite(CS_1, HIGH); // Deselect the flash memory (CS high)
    SPI.end();
}


/*****************************************************************************************
           RETRIVE THE USER DEFINED SYSTEM LOCK PASSWORD
 *****************************************************************************************/
//NEED TO TEST WILL FRESH SPI FLASH MEMORY.
String loadlockPasswordFromFlash() {
  SPI.begin();
  delay(100);
  digitalWrite(CS_1, LOW);

  String password = "";
  char ch = flash.readByte(LOCKPASSWORD_ADDRESS); // Read first byte

  // If first byte is 0xFF or 0x00 → flash empty
  if (ch == 0xFF || ch == 0x00) {
    digitalWrite(CS_1, HIGH);
    SPI.end();
    password = "1000";
    storelockPasswordInFlash(password);
    Serial.println("Flash empty → Default password stored: 1000");
    return password;
  }

  // Otherwise read normally
  for (int i = 0; i < 10; i++) {
    ch = flash.readByte(LOCKPASSWORD_ADDRESS + i);
    if (ch == '\0') break;
    password += ch;
  }

  digitalWrite(CS_1, HIGH);
  SPI.end();

  Serial.print("Loaded password: "); Serial.println(password);
  return password;
}


 /*String loadlockPasswordFromFlash() {
  SPI.begin();
  delay(100);
    digitalWrite(CS_1, LOW);  // Select the flash memory (CS low)
    
    String password = "";
    char ch;
    
    for (int i = 0; i < 10; i++) {  // Assuming max password length is 10
        ch = flash.readByte(LOCKPASSWORD_ADDRESS + i); // Read from correct address
        if (ch == '\0') {
            break;  // Stop reading when null terminator is found
        }
        password += ch;  // Append each character to the string
    }
    
    digitalWrite(CS_1, HIGH); // Deselect the flash memory (CS high)
    
    Serial.print("Loaded lock password: "); Serial.println(password);
    return password;  // Return the loaded password
    SPI.end();
}*/


/*****************************************************************************************
           STORES THE BOOL VARIABLE OF SYSTEM LOCK PASSWORD
 *****************************************************************************************/
void storeLockStatus(bool isLocked) {
    SPI.begin();
    uint32_t lockAddress = LOCK_STATUS_ADDRESS;

    byte lockStatusByte = isLocked ? 1 : 0;  // Convert boolean to byte (1 for true, 0 for false)

    digitalWrite(CS_1, LOW);
    flash.eraseSector(lockAddress); // Erase the sector before writing

    // Write the lock status byte to flash memory
    flash.writeByte(lockAddress, lockStatusByte);

    digitalWrite(CS_1, HIGH);
    SPI.end();

    Serial.println("Stored lock status in Flash:");
    Serial.print("isLocked: "); Serial.println(isLocked ? "true" : "false");
}

/*****************************************************************************************
           RETRIVE THE BOOL VARIABLE OF SYSTEM LOCK PASSWORD
 *****************************************************************************************/
void loadLockStatus(bool *isLocked) {
    SPI.begin();
    uint32_t lockAddress = LOCK_STATUS_ADDRESS;

    digitalWrite(CS_1, LOW);

    // Read the lock status byte from flash memory
    byte lockStatusByte = flash.readByte(lockAddress);

    digitalWrite(CS_1, HIGH);

    // Convert byte back to boolean
    *isLocked = (lockStatusByte == 1);

    SPI.end();

    Serial.println("Loaded lock status from Flash:");
    Serial.print("isLocked: "); Serial.println(*isLocked ? "true" : "false");
}

/*****************************************************************************************
           SETTING THE SET TIME AND DURATION FOR PUMP1 (COMMON)
 *****************************************************************************************/
// Update the pump schedule and store it in SPI flash
void updatePumpSchedule(String command) {
  if (command.startsWith("PUMP:")) {
    
    int hour = command.substring(5, 7).toInt();
    int minute = command.substring(8, 10).toInt();
    String durationStr = command.substring(11); // Extract duration in HH:MM format
    int durationHours = durationStr.substring(0, durationStr.indexOf(':')).toInt();
    int durationMinutes = durationStr.substring(durationStr.indexOf(':') + 1).toInt();

    pump1StartHour = hour;
    pump1StartMinute = minute;
    pump1DurationMinutes = (durationHours * 60) + durationMinutes; // Total duration in minutes
    //savePump1Schedule(); // Save the schedule to SPI flash
    storePump1Data(pump1StartHour, pump1StartMinute, pump1DurationMinutes, pump1RemainingTime); // Store updated data in flash
    saveRemainingTime1(0, PUMP1_REMAINING_TIME_ADDRESS);
    loadRemainingTime1();
    pump1Running = false; //false
    TIMEROFF();
    /*logicActivated = true;
    selectedLogic = 4;*/

    Serial.println("Pump schedule updated.");
    Serial.print("Start time: "); Serial.print(pump1StartHour); Serial.print(":"); Serial.println(pump1StartMinute);
    Serial.print("Duration: "); Serial.print(durationHours); Serial.print(":"); Serial.println(durationMinutes);
  }

}

/*****************************************************************************************
           SETTING THE SET TIME AND DURATION FOR BPUMP (COMMON)
 *****************************************************************************************/
// Update the pump schedule and store it in SPI flash
void BupdatePumpSchedule(String command) {
  if (command.startsWith("BPUMP:")) {
    
    int Bhour = command.substring(6, 8).toInt();
    int Bminute = command.substring(9, 11).toInt();
    String BdurationStr = command.substring(12); // Extract duration in HH:MM format
    int BdurationHours = BdurationStr.substring(0, BdurationStr.indexOf(':')).toInt();
    int BdurationMinutes = BdurationStr.substring(BdurationStr.indexOf(':') + 1).toInt();

    Bpump1StartHour = Bhour;
    Bpump1StartMinute = Bminute;
    Bpump1DurationMinutes = (BdurationHours * 60) + BdurationMinutes; // Total duration in minutes
    //savePump1Schedule(); // Save the schedule to SPI flash
    BstorePump1Data(Bpump1StartHour, Bpump1StartMinute, Bpump1DurationMinutes, Bpump1RemainingTime); // Store updated data in flash
    BsaveRemainingTime1(0, BPUMP1_REMAINING_TIME_ADDRESS);
    BloadRemainingTime1();
     Bpump1Running = false; //false
     //TIMEROFF();
     /*logicActivated = true;
     selectedLogic = 5;*/
    
    Serial.println("Pump schedule updated2.");
    Serial.print("Start time2: "); Serial.print(Bpump1StartHour); Serial.print(":"); Serial.println(Bpump1StartMinute);
    Serial.print("Duration2: "); Serial.print(BdurationHours); Serial.print(":"); Serial.println(BdurationMinutes);
  }

}

/*****************************************************************************************
           SETTING THE SET TIME AND DURATION FOR CPUMP (COMMON)
 *****************************************************************************************/
// Update the pump schedule and store it in SPI flash
void CupdatePumpSchedule(String command) {
  if (command.startsWith("CPUMP:")) {
    
    int Chour = command.substring(6, 8).toInt();
    int Cminute = command.substring(9, 11).toInt();
    String CdurationStr = command.substring(12); // Extract duration in HH:MM format
    int CdurationHours = CdurationStr.substring(0, CdurationStr.indexOf(':')).toInt();
    int CdurationMinutes = CdurationStr.substring(CdurationStr.indexOf(':') + 1).toInt();

    Cpump1StartHour = Chour;
    Cpump1StartMinute = Cminute;
    Cpump1DurationMinutes = (CdurationHours * 60) + CdurationMinutes; // Total duration in minutes
    //savePump1Schedule(); // Save the schedule to SPI flash
    CstorePump1Data(Cpump1StartHour, Cpump1StartMinute, Cpump1DurationMinutes, Cpump1RemainingTime); // Store updated data in flash
    CsaveRemainingTime1(0, CPUMP1_REMAINING_TIME_ADDRESS);
    CloadRemainingTime1();
    Cpump1Running = false; //false
    //TIMEROFF();
    /*logicActivated = true;
    selectedLogic = 6;*/
    
    Serial.println("Pump schedule updated3.");
    Serial.print("Start time3: "); Serial.print(Cpump1StartHour); Serial.print(":"); Serial.println(Cpump1StartMinute);
    Serial.print("Duration3: "); Serial.print(CdurationHours); Serial.print(":"); Serial.println(CdurationMinutes);
  }

}

/*****************************************************************************************
           CHECKING THE SET TIME AND DURATION WITH CURRENT TIME FOR PUMP1 (COMMON)
 *****************************************************************************************/
void checkPumps() {
  int currentHour = hour();
  int currentMinute = minute();
  
  // Pump1 start logic
  if (!pump1Running && currentHour == pump1StartHour && currentMinute == pump1StartMinute) {
    if(pump1DurationMinutes > 0){
    pump1Running = true;
    pump1Counter = pump1DurationMinutes; // Initialize countdown timer
    TIMERMODEPUMP();
    Serial.println("Pump started.");
    //logicActivated = true;
    //selectedLogic = 4;
    pump1MissedSent = true;
    savePump1MissedFlag(true);
    }
  }
}

/*****************************************************************************************
           CHECKING THE SET TIME AND DURATION WITH CURRENT TIME FOR BPUMP (COMMON)
 *****************************************************************************************/
void BcheckPumps() {
  int BcurrentHour = hour();
  int BcurrentMinute = minute();
  
  // Pump1 start logic
  if (!Bpump1Running && BcurrentHour == Bpump1StartHour && BcurrentMinute == Bpump1StartMinute) {
    if(Bpump1DurationMinutes){
    Bpump1Running = true;
    Bpump1Counter = Bpump1DurationMinutes; // Initialize countdown timer
    TIMERMODEPUMP();
    Serial.println("Pump started2.");
    //logicActivated = true;
    //selectedLogic = 5;
    Bpump1MissedSent = true;
    saveBPumpMissedFlag(true);
    }
  }
}

/*****************************************************************************************
           CHECKING THE SET TIME AND DURATION WITH CURRENT TIME FOR CPUMP (COMMON)
 *****************************************************************************************/
void CcheckPumps() {
  int CcurrentHour = hour();
  int CcurrentMinute = minute();
  
  // Pump1 start logic
  if (!Cpump1Running && CcurrentHour == Cpump1StartHour && CcurrentMinute == Cpump1StartMinute) {
    if(Cpump1DurationMinutes){
    Cpump1Running = true;
    Cpump1Counter = Cpump1DurationMinutes; // Initialize countdown timer
    TIMERMODEPUMP();
    Serial.println("Pump started3.");
    //logicActivated = true;
    //selectedLogic = 6;
    Cpump1MissedSent = true;
    saveCPumpMissedFlag(true);
    }
  }
}

/*****************************************************************************************
           UPDATE THE COUNTER EVERY 1MIN FOR PUMP1
 *****************************************************************************************/
void updateCountdown() {
 
  unsigned long currentMillis6 = millis();
  
  // Check if it's time to update the countdown (every minute)
  if (currentMillis6 - lastCountdownTime >= COUNTDOWN_INTERVAL) {
     lastCountdownTime = currentMillis6;

    // Pump1 Countdown Logic
    if (pump1Running && pump1Counter > 0) {
      pump1Counter--;
      Serial.print("Pump Counter: ");
      Serial.println(pump1Counter);
      //saveRemainingTime1(pump1Counter, PUMP1_REMAINING_TIME_ADDRESS);
      // Save to flash periodically (e.g., every 1 minutes)
      if (pump1Counter % 1 == 0) {
        saveRemainingTime1(pump1Counter, PUMP1_REMAINING_TIME_ADDRESS);

    // Create SMS text
  /*char smsBuffer1[50];
  sprintf(smsBuffer1, "Pump1 Remaining Time:%d", pump1Counter);
  // Send SMS to all allowed numbers
  for (int i = 0; i < numAllowedNumbers; i++) {
    fona.sendSMS(allowedPhoneNumbers[i], smsBuffer1);
  }*/
        //SerialBT.println("REMAINING TIME: " + String(pump1Counter));
      }

      // Stop Pump1 when counter reaches zero
      if (pump1Counter == 0) {
        pump1Running = false;
        TIMEROFF();
        //logicActivated = true;
        //selectedLogic = 4;
        Serial.println("Pump stopped due to countdown reaching zero.");
      
      }
    }

  }
}

/*****************************************************************************************
           UPDATE THE COUNTER EVERY 1MIN FOR BPUMP
 *****************************************************************************************/
void BupdateCountdown() {
    
  unsigned long currentMillis4 = millis();
  
  // Check if it's time to update the countdown (every minute)
  if (currentMillis4 - BlastCountdownTime >= BCOUNTDOWN_INTERVAL) {
     BlastCountdownTime = currentMillis4;

    // Pump1 Countdown Logic
    if (Bpump1Running && Bpump1Counter > 0) {
      Bpump1Counter--;
      Serial.print("Pump Counter2: ");
      Serial.println(Bpump1Counter);
      //saveRemainingTime1(pump1Counter, PUMP1_REMAINING_TIME_ADDRESS);
      // Save to flash periodically (e.g., every 5 minutes)
      if (Bpump1Counter % 1 == 0) {
        BsaveRemainingTime1(Bpump1Counter, BPUMP1_REMAINING_TIME_ADDRESS);

         // Create SMS text
  /*char smsBuffer1[50];
  sprintf(smsBuffer1, "BPump Remaining Time:%d", Bpump1Counter);
  // Send SMS to all allowed numbers
  for (int i = 0; i < numAllowedNumbers; i++) {
    fona.sendSMS(allowedPhoneNumbers[i], smsBuffer1);
  }*/
        //SerialBT.println("REMAINING TIME: " + String(pump1Counter));
      }

      // Stop Pump1 when counter reaches zero
      if (Bpump1Counter == 0) {
        Bpump1Running = false;
        TIMEROFF();
        //logicActivated = true;
        //selectedLogic = 5;
        Serial.println("Pump stopped due to countdown reaching zero 2.");
      }
    }

  }
}

/*****************************************************************************************
           UPDATE THE COUNTER EVERY 1MIN FOR CPUMP
 *****************************************************************************************/
void CupdateCountdown() {
    
  unsigned long currentMillis5 = millis();
  
  // Check if it's time to update the countdown (every minute)
  if (currentMillis5 - ClastCountdownTime >= CCOUNTDOWN_INTERVAL) {
     ClastCountdownTime = currentMillis5;

    // Pump1 Countdown Logic
    if (Cpump1Running && Cpump1Counter > 0) {
      Cpump1Counter--;
      Serial.print("Pump Counter3: ");
      Serial.println(Cpump1Counter);
      //saveRemainingTime1(pump1Counter, PUMP1_REMAINING_TIME_ADDRESS);
      // Save to flash periodically (e.g., every 5 minutes)
      if (Cpump1Counter % 1 == 0) {
        CsaveRemainingTime1(Cpump1Counter, CPUMP1_REMAINING_TIME_ADDRESS);

         // Create SMS text
  /*char smsBuffer1[50];
  sprintf(smsBuffer1, "CPump Remaining Time:%d", Cpump1Counter);
  // Send SMS to all allowed numbers
  for (int i = 0; i < numAllowedNumbers; i++) {
    fona.sendSMS(allowedPhoneNumbers[i], smsBuffer1);
  }*/
        //SerialBT.println("REMAINING TIME: " + String(pump1Counter));
      }

      // Stop Pump1 when counter reaches zero
      if (Cpump1Counter == 0) {
        Cpump1Running = false;
        TIMEROFF();
        //logicActivated = true;
        //selectedLogic = 6;
        Serial.println("Pump stopped due to countdown reaching zero 3.");
      }
    }

  }
}

/*****************************************************************************************
           STORE THE SET TIME AND DURATION FOR PUMP1
 *****************************************************************************************/
// Function to store Pump1 data in SPI flash
void storePump1Data(int startHour, int startMinute, int durationMinutes, unsigned long remainingTime) 
{
  SPI.begin();
  digitalWrite(CS_1, LOW);
  flash.eraseSector(PUMP1_DATA_ADDR); // Erase the memory sector for Pump1
  flash.writeByte(PUMP1_DATA_ADDR, startHour);
  flash.writeByte(PUMP1_DATA_ADDR + 1, startMinute);
  flash.writeByte(PUMP1_DATA_ADDR + 2, durationMinutes & 0xFF);       // Lower byte
  flash.writeByte(PUMP1_DATA_ADDR + 3, (durationMinutes >> 8) & 0xFF); // Upper byte

  SPI.end();
  digitalWrite(CS_1, HIGH);
  
  // Print stored data
  Serial.println("Pump Data Stored:");
  Serial.print("Start Hour: "); Serial.println(startHour);
  Serial.print("Start Minute: "); Serial.println(startMinute);
  Serial.print("Duration (minutes): "); Serial.println(durationMinutes);

}

/*****************************************************************************************
           STORE THE SET TIME AND DURATION FOR BPUMP
 *****************************************************************************************/
void BstorePump1Data(int BstartHour, int BstartMinute, int BdurationMinutes, unsigned long BremainingTime) 
{
  SPI.begin();
  digitalWrite(CS_1, LOW);
  flash.eraseSector(BPUMP1_DATA_ADDR); // Erase the memory sector for Pump1
  flash.writeByte(BPUMP1_DATA_ADDR, BstartHour);
  flash.writeByte(BPUMP1_DATA_ADDR + 1, BstartMinute);
  flash.writeByte(BPUMP1_DATA_ADDR + 2, BdurationMinutes & 0xFF);       // Lower byte
  flash.writeByte(BPUMP1_DATA_ADDR + 3, (BdurationMinutes >> 8) & 0xFF); // Upper byte

  SPI.end();
  digitalWrite(CS_1, HIGH);
  
  // Print stored data
  Serial.println("Pump Data Stored2:");
  Serial.print("Start Hour2: "); Serial.println(BstartHour);
  Serial.print("Start Minute2: "); Serial.println(BstartMinute);
  Serial.print("Duration (minutes2): "); Serial.println(BdurationMinutes);

}

/*****************************************************************************************
           STORE THE SET TIME AND DURATION FOR CPUMP
 *****************************************************************************************/
void CstorePump1Data(int CstartHour, int CstartMinute, int CdurationMinutes, unsigned long CremainingTime) 
{
  SPI.begin();
  digitalWrite(CS_1, LOW);
  flash.eraseSector(CPUMP1_DATA_ADDR); // Erase the memory sector for Pump1
  flash.writeByte(CPUMP1_DATA_ADDR, CstartHour);
  flash.writeByte(CPUMP1_DATA_ADDR + 1, CstartMinute);
  flash.writeByte(CPUMP1_DATA_ADDR + 2, CdurationMinutes & 0xFF);       // Lower byte
  flash.writeByte(CPUMP1_DATA_ADDR + 3, (CdurationMinutes >> 8) & 0xFF); // Upper byte

  SPI.end();
  digitalWrite(CS_1, HIGH);
  
  // Print stored data
  Serial.println("Pump Data Stored3:");
  Serial.print("Start Hour3: "); Serial.println(CstartHour);
  Serial.print("Start Minute3: "); Serial.println(CstartMinute);
  Serial.print("Duration (minutes3): "); Serial.println(CdurationMinutes);

}
/*****************************************************************************************
           RETRIVE THE SET TIME AND DURATION FOR PUMP1
 *****************************************************************************************/
// Function to retrieve Pump1 data from SPI flash
void retrievePump1Data(int &startHour, int &startMinute, int &durationMinutes, unsigned long &remainingTime)
{
  SPI.begin();
  digitalWrite(CS_1, LOW);
  startHour = flash.readByte(PUMP1_DATA_ADDR);
  startMinute = flash.readByte(PUMP1_DATA_ADDR + 1);
  durationMinutes = flash.readByte(PUMP1_DATA_ADDR + 2) | (flash.readByte(PUMP1_DATA_ADDR + 3) << 8);

  SPI.end();
  digitalWrite(CS_1, HIGH);
  
  // Print retrieved data
  Serial.println("Pump Data Retrieved:");
  Serial.print("Start Hour: "); Serial.println(startHour);
  Serial.print("Start Minute: "); Serial.println(startMinute);
  Serial.print("Duration (minutes): "); Serial.println(durationMinutes);

}
/*****************************************************************************************
           RETRIVE THE SET TIME AND DURATION FOR BPUMP
 *****************************************************************************************/
void BretrievePump1Data(int &BstartHour, int &BstartMinute, int &BdurationMinutes, unsigned long &BremainingTime)
{
  SPI.begin();
  digitalWrite(CS_1, LOW);
  BstartHour = flash.readByte(BPUMP1_DATA_ADDR);
  BstartMinute = flash.readByte(BPUMP1_DATA_ADDR + 1);
  BdurationMinutes = flash.readByte(BPUMP1_DATA_ADDR + 2) | (flash.readByte(BPUMP1_DATA_ADDR + 3) << 8);

  SPI.end();
  digitalWrite(CS_1, HIGH);
  
  // Print retrieved data
  Serial.println("Pump Data Retrieved2:");
  Serial.print("Start Hour2: "); Serial.println(BstartHour);
  Serial.print("Start Minute2: "); Serial.println(BstartMinute);
  Serial.print("Duration (minutes2): "); Serial.println(BdurationMinutes);

}
/*****************************************************************************************
           RETRIVE THE SET TIME AND DURATION FOR CPUMP
 *****************************************************************************************/
void CretrievePump1Data(int &CstartHour, int &CstartMinute, int &CdurationMinutes, unsigned long &CremainingTime)
{
  SPI.begin();
  digitalWrite(CS_1, LOW);
  CstartHour = flash.readByte(CPUMP1_DATA_ADDR);
  CstartMinute = flash.readByte(CPUMP1_DATA_ADDR + 1);
  CdurationMinutes = flash.readByte(CPUMP1_DATA_ADDR + 2) | (flash.readByte(CPUMP1_DATA_ADDR + 3) << 8);

  SPI.end();
  digitalWrite(CS_1, HIGH);
  
  // Print retrieved data
  Serial.println("Pump Data Retrieved3:");
  Serial.print("Start Hour3: "); Serial.println(CstartHour);
  Serial.print("Start Minute3: "); Serial.println(CstartMinute);
  Serial.print("Duration (minutes3): "); Serial.println(CdurationMinutes);

}
/*****************************************************************************************
           STORE THE REMAINING TIME FOR PUMP1
 *****************************************************************************************/
void saveRemainingTime1(unsigned long remainingTime, uint32_t address) {
  SPI.begin();
  digitalWrite(CS_1, LOW);
  flash.eraseSector(address); // Erase the sector to prepare for writing
  flash.writeByte(address, remainingTime & 0xFF);         // Lower byte
  flash.writeByte(address + 1, (remainingTime >> 8) & 0xFF); // Upper byte
  digitalWrite(CS_1, HIGH);
  SPI.end();

  Serial.print("Pump remaining time saved: ");
  Serial.println(remainingTime);
}

/*****************************************************************************************
           STORE THE REMAINING TIME FOR BPUMP
 *****************************************************************************************/
void BsaveRemainingTime1(unsigned long BremainingTime, uint32_t Baddress) {
  SPI.begin();
  digitalWrite(CS_1, LOW);
  flash.eraseSector(Baddress); // Erase the sector to prepare for writing
  flash.writeByte(Baddress, BremainingTime & 0xFF);         // Lower byte
  flash.writeByte(Baddress + 1, (BremainingTime >> 8) & 0xFF); // Upper byte
  digitalWrite(CS_1, HIGH);
  SPI.end();

  Serial.print("Pump remaining time saved2: ");
  Serial.println(BremainingTime);
}

/*****************************************************************************************
           STORE THE REMAINING TIME FOR CPUMP
 *****************************************************************************************/
void CsaveRemainingTime1(unsigned long CremainingTime, uint32_t Caddress) {
  SPI.begin();
  digitalWrite(CS_1, LOW);
  flash.eraseSector(Caddress); // Erase the sector to prepare for writing
  flash.writeByte(Caddress, CremainingTime & 0xFF);         // Lower byte
  flash.writeByte(Caddress + 1, (CremainingTime >> 8) & 0xFF); // Upper byte
  digitalWrite(CS_1, HIGH);
  SPI.end();

  Serial.print("Pump remaining time saved3: ");
  Serial.println(CremainingTime);
}

/*****************************************************************************************
           RETRIVE THE REMAINING TIME FOR PUMP1
 *****************************************************************************************/
void loadRemainingTime1() {
  SPI.begin();
  uint32_t address = PUMP1_REMAINING_TIME_ADDRESS; // Address for Pump 1
  digitalWrite(CS_1, LOW);
  pump1Counter = flash.readByte(address) | (flash.readByte(address + 1) << 8); // Read 16-bit value
  digitalWrite(CS_1, HIGH);
  SPI.end();

  Serial.println("Pump remaining time loaded from flash.");
  Serial.print("Remaining time: ");
  Serial.println(pump1Counter);
}

/*****************************************************************************************
           RETRIVE THE REMAINING TIME FOR BPUMP
 *****************************************************************************************/
/////////////////////////////2ND TIMER///////////////////////
void BloadRemainingTime1() {
  SPI.begin();
  uint32_t Baddress = BPUMP1_REMAINING_TIME_ADDRESS; // Address for Pump 1
  digitalWrite(CS_1, LOW);
  Bpump1Counter = flash.readByte(Baddress) | (flash.readByte(Baddress + 1) << 8); // Read 16-bit value
  digitalWrite(CS_1, HIGH);
  SPI.end();

  Serial.println("Pump remaining time loaded from flash2.");
  Serial.print("Remaining time2: ");
  Serial.println(Bpump1Counter);
}

/*****************************************************************************************
           RETRIVE THE REMAINING TIME FOR CPUMP
 *****************************************************************************************/
///////////////////////////3RD TIMER//////////////////////////////
void CloadRemainingTime1() {
  SPI.begin();
  uint32_t Caddress = CPUMP1_REMAINING_TIME_ADDRESS; // Address for Pump 1
  digitalWrite(CS_1, LOW);
  Cpump1Counter = flash.readByte(Caddress) | (flash.readByte(Caddress + 1) << 8); // Read 16-bit value
  digitalWrite(CS_1, HIGH);
  SPI.end();

  Serial.println("Pump remaining time loaded from flash3.");
  Serial.print("Remaining time3: ");
  Serial.println(Cpump1Counter);
}

/*****************************************************************************************
TIMER SETUP, POWER CUT OFF AND COME BACK CALCULATES THE REMAINING TIME AND UPDATES THE COUNTER
 *****************************************************************************************/
void TIMERSETUP() {
  // Retrieve stored schedules and load saved remaining times
  retrievePump1Data(pump1StartHour, pump1StartMinute, pump1DurationMinutes, pump1RemainingTime);
  loadRemainingTime1();
  savedRemainingPump1_global = pump1Counter;
  pump1PostBootPending = true;
  unsigned long savedPump1 = pump1Counter;
  
  BretrievePump1Data(Bpump1StartHour, Bpump1StartMinute, Bpump1DurationMinutes, Bpump1RemainingTime);
  BloadRemainingTime1();  
  savedRemainingBPump_global = Bpump1Counter;
  BpumpPostBootPending = true;
  unsigned long savedPumpB = Bpump1Counter;

  CretrievePump1Data(Cpump1StartHour, Cpump1StartMinute, Cpump1DurationMinutes, Cpump1RemainingTime);
  CloadRemainingTime1();  
  savedRemainingCPump_global = Cpump1Counter;
  CpumpPostBootPending = true;
  unsigned long savedPumpC = Cpump1Counter;


  // Calculate remaining time according to system clock (window-based)
  //int calcPump1 = calculateRemaining(pump1StartHour, pump1StartMinute, pump1DurationMinutes);
  //int calcPumpB = calculateRemaining(Bpump1StartHour, Bpump1StartMinute, Bpump1DurationMinutes);
  //int calcPumpC = calculateRemaining(Cpump1StartHour, Cpump1StartMinute, Cpump1DurationMinutes);

  // Count how many timers are configured
  int activeTimers = 0;
  if (pump1DurationMinutes  > 0) activeTimers++;
  if (Bpump1DurationMinutes > 0) activeTimers++;
  if (Cpump1DurationMinutes > 0) activeTimers++;

  // Helper: check if a pump had been running before outage
  auto wasRunningBefore = [](unsigned long savedRemaining, int duration)->bool {
    return (savedRemaining > 0 && savedRemaining <= (unsigned long)duration);
  };

  int nowMinutes = hour() * 60 + minute();

  // ---------- Multi-timer mode (>=2 timers) ----------
if (activeTimers > 1) {
  pump1Running  = false;
  Bpump1Running = false;
  Cpump1Running = false;

 // ---- Pump1 ----
{
  int startMin = pump1StartHour * 60 + pump1StartMinute;
  int endMin   = startMin + pump1DurationMinutes;

  if (nowMinutes < startMin) {
    // Before slot
    pump1Counter = 0;
    pump1Running = false;
  }
  else if (nowMinutes >= startMin && nowMinutes < endMin) { // STRICT < end
    // compute remaining according to clock
    int calcRemaining = calculateRemaining(pump1StartHour, pump1StartMinute, pump1DurationMinutes);

    if (calcRemaining > 0) {
      pump1Counter = calcRemaining;
      pump1Running = true;
      TIMERMODEPUMP();
      Serial.println("Pump1 resumed (multi-mode).");
      // keep any other flags you need here (varpumpmissed etc.) if desired
    } else {
      // nothing to run (edge case), keep pump off
      pump1Counter = 0;
      pump1Running = false;
      
    }
  }
  else {
    // After slot
    pump1Counter = 0;
    pump1Running = false;
   
  }
}

  // ---- BPump ----
{
  int startMin = Bpump1StartHour * 60 + Bpump1StartMinute;
  int endMin   = startMin + Bpump1DurationMinutes;

  if (nowMinutes < startMin) {
    Bpump1Counter = 0;
    Bpump1Running = false;
  }
  else if (nowMinutes >= startMin && nowMinutes < endMin) {
    int calcRemaining = calculateRemaining(Bpump1StartHour, Bpump1StartMinute, Bpump1DurationMinutes);

    if (calcRemaining > 0) {
      Bpump1Counter = calcRemaining;
      Bpump1Running = true;
      TIMERMODEPUMP();
      Serial.println("BPump resumed (multi-mode).");
    } else {
      Bpump1Counter = 0;
      Bpump1Running = false;
      
    }
  }
  else {
    Bpump1Counter = 0;
    Bpump1Running = false;
   
  }
}

// ---- CPump ----
{
  int startMin = Cpump1StartHour * 60 + Cpump1StartMinute;
  int endMin   = startMin + Cpump1DurationMinutes;

  if (nowMinutes < startMin) {
    Cpump1Counter = 0;
    Cpump1Running = false;
  }
  else if (nowMinutes >= startMin && nowMinutes < endMin) {
    int calcRemaining = calculateRemaining(Cpump1StartHour, Cpump1StartMinute, Cpump1DurationMinutes);

    if (calcRemaining > 0) {
      Cpump1Counter = calcRemaining;
      Cpump1Running = true;
      TIMERMODEPUMP();
      Serial.println("CPump resumed (multi-mode).");
    } else {
      Cpump1Counter = 0;
      Cpump1Running = false;
      
    }
  }
  else {
    Cpump1Counter = 0;
    Cpump1Running = false;
    
  }
}

}

  // ---------- Single-timer mode (==1 timer) ----------
else if (activeTimers == 1) {

  // ----- Pump1 only -----
  if (pump1DurationMinutes > 0 && Bpump1DurationMinutes == 0 && Cpump1DurationMinutes == 0) {
    int startMin = pump1StartHour * 60 + pump1StartMinute;
    int endMin   = startMin + pump1DurationMinutes;

    if (nowMinutes < startMin) {
      pump1Running = false;
      pump1Counter = savedPump1;
    }
    else if (nowMinutes >= startMin && nowMinutes <= endMin) {
      if (wasRunningBefore(savedPump1, pump1DurationMinutes)) {
        pump1Counter = savedPump1;
         pump1Running = true;
      TIMERMODEPUMP();
      pump1MissedSent = true;
      savePump1MissedFlag(true);
      saveRemainingTime1(pump1Counter, PUMP1_REMAINING_TIME_ADDRESS);
      savedRemainingPump1_global = 0;
      Serial.print("Pump1 resumed (single-mode). Remaining: "); Serial.println(pump1Counter);
      }
      else if (!wasRunningBefore(savedPump1, pump1DurationMinutes)) {
        if (nowMinutes >= startMin && nowMinutes < (endMin - 1)){
        pump1Counter = pump1DurationMinutes;
        pump1Running = true;
      TIMERMODEPUMP();
      pump1MissedSent = true;
      savePump1MissedFlag(true);
      saveRemainingTime1(pump1Counter, PUMP1_REMAINING_TIME_ADDRESS);
      savedRemainingPump1_global = 0;
      Serial.print("Pump1 resumed (single-mode). Remaining: "); Serial.println(pump1Counter);
      }
      }  
    }
       else { // after end
      if (wasRunningBefore(savedPump1, pump1DurationMinutes)) {
        pump1Counter = savedPump1;
        pump1Running = true;
        TIMERMODEPUMP();
        pump1MissedSent = true;
        savePump1MissedFlag(true);
        savedRemainingPump1_global = 0;
        Serial.print("Pump1 resumed remaining run after window: "); Serial.println(pump1Counter);
      } else {
        pump1Running = false;
        pump1Counter = 0;
      }
        
    }
  }


  // ----- BPump only -----
  if (Bpump1DurationMinutes > 0 && pump1DurationMinutes == 0 && Cpump1DurationMinutes == 0) {
    int startMin = Bpump1StartHour * 60 + Bpump1StartMinute;
    int endMin   = startMin + Bpump1DurationMinutes;

    if (nowMinutes < startMin) {
      Bpump1Running = false;
      Bpump1Counter = savedPumpB;
    }
    else if (nowMinutes >= startMin && nowMinutes <= endMin) {
      if (wasRunningBefore(savedPumpB, Bpump1DurationMinutes)) {
        Bpump1Counter = savedPumpB;
        Bpump1Running = true;
      TIMERMODEPUMP();
      Bpump1MissedSent = true;
      saveBPumpMissedFlag(true);
      BsaveRemainingTime1(Bpump1Counter, BPUMP1_REMAINING_TIME_ADDRESS);
      savedRemainingBPump_global = 0;
      Serial.print("BPump resumed (single-mode). Remaining: "); Serial.println(Bpump1Counter);
      } 
      else if (!wasRunningBefore(savedPumpB, Bpump1DurationMinutes)) {
        if (nowMinutes >= startMin && nowMinutes < (endMin - 1)){
       Bpump1Counter = Bpump1DurationMinutes;
       Bpump1Running = true;
      TIMERMODEPUMP();
      Bpump1MissedSent = true;
      saveBPumpMissedFlag(true);
      BsaveRemainingTime1(Bpump1Counter, BPUMP1_REMAINING_TIME_ADDRESS);
      savedRemainingBPump_global = 0;
      Serial.print("BPump resumed (single-mode). Remaining: "); Serial.println(Bpump1Counter);
      }
    }
    }
    else { // after end
      if (wasRunningBefore(savedPumpB, Bpump1DurationMinutes)) {
        Bpump1Counter = savedPumpB;
        Bpump1Running = true;
        TIMERMODEPUMP();
        Bpump1MissedSent = true;
        saveBPumpMissedFlag(true);
        savedRemainingBPump_global = 0;
        Serial.print("BPump resumed remaining run after window: "); Serial.println(Bpump1Counter);
      } else {
        Bpump1Running = false;
        Bpump1Counter = 0;
      }
    }
  }

  // ----- CPump only -----
  if (Cpump1DurationMinutes > 0 && pump1DurationMinutes == 0 && Bpump1DurationMinutes == 0) {
    int startMin = Cpump1StartHour * 60 + Cpump1StartMinute;
    int endMin   = startMin + Cpump1DurationMinutes;

    if (nowMinutes < startMin) {
      Cpump1Running = false;
      Cpump1Counter = savedPumpC;
    }
    else if (nowMinutes >= startMin && nowMinutes <= endMin) {
      if (wasRunningBefore(savedPumpC, Cpump1DurationMinutes)) {
        Cpump1Counter = savedPumpC;
        Cpump1Running = true;
      TIMERMODEPUMP();
      Cpump1MissedSent = true;
      saveCPumpMissedFlag(true);
      CsaveRemainingTime1(Cpump1Counter, CPUMP1_REMAINING_TIME_ADDRESS);
      savedRemainingCPump_global = 0;
      Serial.print("CPump resumed (single-mode). Remaining: "); Serial.println(Cpump1Counter);
      } 
     else if (!wasRunningBefore(savedPumpC, Cpump1DurationMinutes)) {
      if (nowMinutes >= startMin && nowMinutes < (endMin - 1)){
         Cpump1Counter = Cpump1DurationMinutes;
         Cpump1Running = true;
      TIMERMODEPUMP();
      Cpump1MissedSent = true;
      saveCPumpMissedFlag(true);
      CsaveRemainingTime1(Cpump1Counter, CPUMP1_REMAINING_TIME_ADDRESS);
      savedRemainingCPump_global = 0;
      Serial.print("CPump resumed (single-mode). Remaining: "); Serial.println(Cpump1Counter);
      }
    }
    }
    else { // after end
      if (wasRunningBefore(savedPumpC, Cpump1DurationMinutes)) {
        Cpump1Counter = savedPumpC;
        Cpump1Running = true;
        TIMERMODEPUMP();
        Cpump1MissedSent = true;
        saveCPumpMissedFlag(true);
        savedRemainingCPump_global = 0;
        Serial.print("CPump resumed remaining run after window: "); Serial.println(Cpump1Counter);
      } else {
        Cpump1Running = false;
        Cpump1Counter = 0;
      }
    }
  }
}
}

/*****************************************************************************************
           POWER CUT OFF AND COME BACK CALCULATES THE REMAINING TIME
 *****************************************************************************************/
int calculateRemaining(int startHour, int startMinute, int durationMinutes) {
  if (startHour < 0 || startMinute < 0 || durationMinutes <= 0) return 0;

  int start = startHour * 60 + startMinute;
  int end = start + durationMinutes;
  int now = hour() * 60 + minute();

  if (now < start) {
    return durationMinutes; // not started yet
  } else if (now >= start && now < end) {
    return end - now; // still running
  } else {
    return 0; // already finished
  }
}

/*****************************************************************************************
           SENDS AN SMS TO USER, PUMP1 MISSIED TIME 
 *****************************************************************************************/
void Pump1Missed() {

  int nowH = hour();
  int nowM = minute();

  if (pump1StartHour >= 0 && pump1StartMinute >= 0 && pump1DurationMinutes > 0) {
    int nowMinutes   = nowH * 60 + nowM;
    int startMinutes = pump1StartHour * 60 + pump1StartMinute;
    int endMinutes   = startMinutes + pump1DurationMinutes;

    // 1) POST-BOOT check: pump was RUNNING before power cut and we just restarted.
    //    Run this ONCE per boot (pump1PostBootPending) and only if savedRemaining indicates the pump had started.
if (pump1PostBootPending && nowMinutes >= startMinutes) {
  // calculate how much would be remaining if pump had been running normally
  int calcRemaining = calculateRemaining(pump1StartHour, pump1StartMinute, pump1DurationMinutes);

  if (savedRemainingPump1_global < (unsigned long)pump1DurationMinutes) {
    if (savedRemainingPump1_global > (unsigned long)calcRemaining) {
      int lostMinutes = (int)(savedRemainingPump1_global - (unsigned long)calcRemaining);
      int lostHours = lostMinutes / 60;
      int lostMins  = lostMinutes % 60;

      char msg[100];
      if (lostHours > 0)
        sprintf(msg, "Pump1 lost %d hr %d min due to power cut (while running)!", lostHours, lostMins);
      else
        sprintf(msg, "Pump1 lost %d min due to power cut (while running)!", lostMins);

      for (int i = 0; i < numAllowedNumbers; i++) {
        fona.sendSMS(allowedPhoneNumbers[i], msg);
      }

      // persist updated remaining so no duplicate
      saveRemainingTime1(calcRemaining, PUMP1_REMAINING_TIME_ADDRESS);
      savedRemainingPump1_global = calcRemaining;
    }
  }
  pump1PostBootPending = false; // run once per boot
}

    // 2) EXISTING logic: "power back during slot when pump never ran before" (Scenario 4)
    //    and "full slot missed" — keep behavior (only send once per day via pump1MissedSent)
     if (!pump1MissedSent) {
      // Case A: Power back during slot (Scenario 4)
      if (nowMinutes > startMinutes && nowMinutes < endMinutes) {
        int lostMinutes = nowMinutes - startMinutes;

        int lostHours = lostMinutes / 60;
        int lostMins  = lostMinutes % 60;

        char msg[80];
        if (lostHours > 0)
          sprintf(msg, "Pump1 lost %d hr %d min due to power cut!", lostHours, lostMins);
        else
          sprintf(msg, "Pump1 lost %d min due to power cut!", lostMins);

        for (int i = 0; i < numAllowedNumbers; i++) {
          fona.sendSMS(allowedPhoneNumbers[i], msg);
        }

        pump1MissedSent = true;
        savePump1MissedFlag(true);
      }
      // Case B: Full slot missed
      else if (nowMinutes >= endMinutes && !pump1Running) {
        for (int i = 0; i < numAllowedNumbers; i++) {
          fona.sendSMS(allowedPhoneNumbers[i], (char*) "Pump1 schedule fully missed!");
        }
        pump1MissedSent = true;
        savePump1MissedFlag(true);
      }
    }
  }

  resetDailyFlags(); // Reset once per day

  if (!powerCutCheckDone && timeStatus() == timeSet) {

    bool wasRunning = pump1Running;   // Pump was ON before power cut?

    if (wasRunning) {

        unsigned long lastSaved = loadLastSavedMinute();
        unsigned long nowEpoch  = now();

        if (lastSaved > 1000 && nowEpoch > lastSaved) {

            unsigned long diff = nowEpoch - lastSaved;   // seconds difference

            if (diff >= 60) {

            unsigned long hours  = diff / 3600;
            unsigned long minutes = (diff % 3600) / 60;

            // -- Format HH:MM --
            char sms[60];
            sprintf(sms, "POWER CUT OF PUMP TIME: %02lu:%02lu", hours, minutes);

            // Send to all users
            for (int i = 0; i < numAllowedNumbers; i++) {
                fona.sendSMS(allowedPhoneNumbers[i], sms);
            }
          }
        }
    }

    powerCutCheckDone = true;   // Send only once per boot
}

}

/*****************************************************************************************
           SENDS AN SMS TO USER, BPUMP MISSIED TIME 
 *****************************************************************************************/
void BPump1Missed() {

  int nowH = hour();
  int nowM = minute();

  if (Bpump1StartHour >= 0 && Bpump1StartMinute >= 0 && Bpump1DurationMinutes > 0) {
    int nowMinutes   = nowH * 60 + nowM;
    int startMinutes = Bpump1StartHour * 60 + Bpump1StartMinute;
    int endMinutes   = startMinutes + Bpump1DurationMinutes;

    // 1) POST-BOOT check: pump was RUNNING before power cut and we just restarted
    if (BpumpPostBootPending && nowMinutes >= startMinutes) {
      int calcRemaining = calculateRemaining(Bpump1StartHour, Bpump1StartMinute, Bpump1DurationMinutes);

      if (savedRemainingBPump_global < (unsigned long)Bpump1DurationMinutes) {
        if (savedRemainingBPump_global > (unsigned long)calcRemaining) {
          int lostMinutes = (int)(savedRemainingBPump_global - (unsigned long)calcRemaining);
          int lostHours = lostMinutes / 60;
          int lostMins  = lostMinutes % 60;

          char msg[100];
          if (lostHours > 0)
            sprintf(msg, "BPump lost %d hr %d min due to power cut (while running)!", lostHours, lostMins);
          else
            sprintf(msg, "BPump lost %d min due to power cut (while running)!", lostMins);

          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], msg);
          }

          BsaveRemainingTime1(calcRemaining, BPUMP1_REMAINING_TIME_ADDRESS);
          savedRemainingBPump_global = calcRemaining;
        }
      }
      BpumpPostBootPending = false;
    }

    // 2) EXISTING logic: "power back during slot when pump never ran before" and "full slot missed"
    if (!Bpump1MissedSent) {
      // Case A: Power back during slot (Scenario 4)
      if (nowMinutes > startMinutes && nowMinutes < endMinutes) {
        int lostMinutes = nowMinutes - startMinutes;

        int lostHours = lostMinutes / 60;
        int lostMins  = lostMinutes % 60;

        char msg[80];
        if (lostHours > 0)
          sprintf(msg, "BPump lost %d hr %d min due to power cut!", lostHours, lostMins);
        else
          sprintf(msg, "BPump lost %d min due to power cut!", lostMins);

        for (int i = 0; i < numAllowedNumbers; i++) {
          fona.sendSMS(allowedPhoneNumbers[i], msg);
        }

        Bpump1MissedSent = true;
        saveBPumpMissedFlag(true);
      }
      // Case B: Full slot missed
      else if (nowMinutes >= endMinutes && !Bpump1Running) {
        for (int i = 0; i < numAllowedNumbers; i++) {
          fona.sendSMS(allowedPhoneNumbers[i], (char*)"BPump schedule fully missed!");
        }
        Bpump1MissedSent = true;
        saveBPumpMissedFlag(true);
      }
    }
  }

  resetDailyFlags(); // Reset once per day

  if (!BpowerCutCheckDone && timeStatus() == timeSet) {

    bool BwasRunning = Bpump1Running;   // Pump was ON before power cut?

    if (BwasRunning) {

        unsigned long lastSaved = loadLastSavedMinute();
        unsigned long nowEpoch  = now();

        if (lastSaved > 1000 && nowEpoch > lastSaved) {

            unsigned long diff = nowEpoch - lastSaved;   // seconds difference

            if (diff >= 60) {

            unsigned long hours  = diff / 3600;
            unsigned long minutes = (diff % 3600) / 60;

            // -- Format HH:MM --
            char sms[60];
            sprintf(sms, "POWER CUT OF BPUMP TIME: %02lu:%02lu", hours, minutes);

            // Send to all users
            for (int i = 0; i < numAllowedNumbers; i++) {
                fona.sendSMS(allowedPhoneNumbers[i], sms);
            }
          }
        }
    }

    BpowerCutCheckDone = true;   // Send only once per boot
}
}

/*****************************************************************************************
           SENDS AN SMS TO USER, CPUMP MISSIED TIME 
 *****************************************************************************************/
void CPump1Missed() {

  int nowH = hour();
  int nowM = minute();

  if (Cpump1StartHour >= 0 && Cpump1StartMinute >= 0 && Cpump1DurationMinutes > 0) {
    int nowMinutes   = nowH * 60 + nowM;
    int startMinutes = Cpump1StartHour * 60 + Cpump1StartMinute;
    int endMinutes   = startMinutes + Cpump1DurationMinutes;

    // 1) POST-BOOT check: pump was RUNNING before power cut and we just restarted
    if (CpumpPostBootPending && nowMinutes >= startMinutes) {
      int calcRemaining = calculateRemaining(Cpump1StartHour, Cpump1StartMinute, Cpump1DurationMinutes);

      if (savedRemainingCPump_global < (unsigned long)Cpump1DurationMinutes) {
        if (savedRemainingCPump_global > (unsigned long)calcRemaining) {
          int lostMinutes = (int)(savedRemainingCPump_global - (unsigned long)calcRemaining);
          int lostHours = lostMinutes / 60;
          int lostMins  = lostMinutes % 60;

          char msg[100];
          if (lostHours > 0)
            sprintf(msg, "CPump lost %d hr %d min due to power cut (while running)!", lostHours, lostMins);
          else
            sprintf(msg, "CPump lost %d min due to power cut (while running)!", lostMins);

          for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], msg);
          }

          CsaveRemainingTime1(calcRemaining, CPUMP1_REMAINING_TIME_ADDRESS);
          savedRemainingCPump_global = calcRemaining;
        }
      }
      CpumpPostBootPending = false;
    }

    // 2) EXISTING logic: "power back during slot when pump never ran before" and "full slot missed"
    if (!Cpump1MissedSent) {
      // Case A: Power back during slot (Scenario 4)
      if (nowMinutes > startMinutes && nowMinutes < endMinutes) {
        int lostMinutes = nowMinutes - startMinutes;

        int lostHours = lostMinutes / 60;
        int lostMins  = lostMinutes % 60;

        char msg[80];
        if (lostHours > 0)
          sprintf(msg, "CPump lost %d hr %d min due to power cut!", lostHours, lostMins);
        else
          sprintf(msg, "CPump lost %d min due to power cut!", lostMins);

        for (int i = 0; i < numAllowedNumbers; i++) {
          fona.sendSMS(allowedPhoneNumbers[i], msg);
        }

        Cpump1MissedSent = true;
        saveCPumpMissedFlag(true);
      }
      // Case B: Full slot missed
      else if (nowMinutes >= endMinutes && !Cpump1Running) {
        for (int i = 0; i < numAllowedNumbers; i++) {
          fona.sendSMS(allowedPhoneNumbers[i], (char*)"CPump schedule fully missed!");
        }
        Cpump1MissedSent = true;
        saveCPumpMissedFlag(true);
      }
    }
  }

  resetDailyFlags(); // Reset once per day

  if (!CpowerCutCheckDone && timeStatus() == timeSet) {

    bool CwasRunning = Cpump1Running;   // Pump was ON before power cut?

    if (CwasRunning) {

        unsigned long lastSaved = loadLastSavedMinute();
        unsigned long nowEpoch  = now();

        if (lastSaved > 1000 && nowEpoch > lastSaved) {

            unsigned long diff = nowEpoch - lastSaved;   // seconds difference

            if (diff >= 60) {

            unsigned long hours  = diff / 3600;
            unsigned long minutes = (diff % 3600) / 60;

            // -- Format HH:MM --
            char sms[60];
            sprintf(sms, "POWER CUT OF CPUMP TIME: %02lu:%02lu", hours, minutes);

            // Send to all users
            for (int i = 0; i < numAllowedNumbers; i++) {
                fona.sendSMS(allowedPhoneNumbers[i], sms);
            }
          }
        }
    }

    CpowerCutCheckDone = true;   // Send only once per boot
}
}

/*****************************************************************************************
           STORE MISSED TIME BOOL FLAG FOR PUMP1
 *****************************************************************************************/
void savePump1MissedFlag(bool flag) {
  SPI.begin();
  digitalWrite(CS_1, LOW);
  flash.eraseSector(PUMP1_MISSED_FLAG_ADDR);
  flash.writeByte(PUMP1_MISSED_FLAG_ADDR, flag ? 1 : 0);
  digitalWrite(CS_1, HIGH);
  SPI.end();
}

/*****************************************************************************************
           RETRIVE'S MISSED TIME BOOL FLAG FOR PUMP1
 *****************************************************************************************/
bool loadPump1MissedFlag() {
  SPI.begin();
  digitalWrite(CS_1, LOW);
  uint8_t val = flash.readByte(PUMP1_MISSED_FLAG_ADDR);
  digitalWrite(CS_1, HIGH);
  SPI.end();
  return (val == 1);
}

/*****************************************************************************************
           STORE MISSED TIME BOOL FLAG FOR BPUMP
 *****************************************************************************************/
void saveBPumpMissedFlag(bool flag) {
  SPI.begin();
  digitalWrite(CS_1, LOW);
  flash.eraseSector(BPUMP1_MISSED_FLAG_ADDR);
  flash.writeByte(BPUMP1_MISSED_FLAG_ADDR, flag ? 1 : 0);
  digitalWrite(CS_1, HIGH);
  SPI.end();
}

/*****************************************************************************************
           RETRIVE'S MISSED TIME BOOL FLAG FOR BPUMP
 *****************************************************************************************/
bool loadBPumpMissedFlag() {
  SPI.begin();
  digitalWrite(CS_1, LOW);
  uint8_t val = flash.readByte(BPUMP1_MISSED_FLAG_ADDR);
  digitalWrite(CS_1, HIGH);
  SPI.end();
  return (val == 1);
}

/*****************************************************************************************
           STORE MISSED TIME BOOL FLAG FOR CPUMP
 *****************************************************************************************/
void saveCPumpMissedFlag(bool flag) {
  SPI.begin();
  digitalWrite(CS_1, LOW);
  flash.eraseSector(CPUMP1_MISSED_FLAG_ADDR);
  flash.writeByte(CPUMP1_MISSED_FLAG_ADDR, flag ? 1 : 0);
  digitalWrite(CS_1, HIGH);
  SPI.end();
}

/*****************************************************************************************
           RETRIVE'S MISSED TIME BOOL FLAG FOR CPUMP
 *****************************************************************************************/
bool loadCPumpMissedFlag() {
  SPI.begin();
  digitalWrite(CS_1, LOW);
  uint8_t val = flash.readByte(CPUMP1_MISSED_FLAG_ADDR);
  digitalWrite(CS_1, HIGH);
  SPI.end();
  return (val == 1);
}

/*****************************************************************************************
           RESET THE MISSED TIME BOOL FLAG AFTER 24 HOURS
 *****************************************************************************************/
///////////////// DAILY RESET //////////////////
void resetDailyFlags() {
  int today = day();
  if (today != lastSavedDay) {
    pump1MissedSent  = false; savePump1MissedFlag(false);
    Bpump1MissedSent = false; saveBPumpMissedFlag(false);
    Cpump1MissedSent = false; saveCPumpMissedFlag(false);

    lastSavedDay = today;
    saveLastDay(today);
  }
}

/*****************************************************************************************
           STORE THE PRESENT DAY
 *****************************************************************************************/
// Save/Load last reset day
void saveLastDay(int day) {
  SPI.begin();
  digitalWrite(CS_1, LOW);
  flash.eraseSector(LAST_RESET_DAY_ADDR);
  flash.writeByte(LAST_RESET_DAY_ADDR, (uint8_t)day);
  digitalWrite(CS_1, HIGH);
  SPI.end();
}

/*****************************************************************************************
           RETRIVES THE PRESENT DAY
 *****************************************************************************************/
int loadLastDay() {
  SPI.begin();
  digitalWrite(CS_1, LOW);
  uint8_t val = flash.readByte(LAST_RESET_DAY_ADDR);
  digitalWrite(CS_1, HIGH);
  SPI.end();
  return (int)val;
}


/*****************************************************************************************
           STORE THE CURRENT TIME
 *****************************************************************************************/
void saveCurrentMinuteToFlash() {
    SPI.begin();
    digitalWrite(CS_1, LOW);
    unsigned long nowEpoch = now();
    flash.eraseSector(LAST_POWER_SAVE_ADDR);
    flash.writeLong(LAST_POWER_SAVE_ADDR, nowEpoch);
    digitalWrite(CS_1, HIGH);
    SPI.end();
    Serial.println("save Current Minute To Flash:");
    Serial.println(nowEpoch);
}

/*****************************************************************************************
           RETRIVES THE CURRENT TIME
 *****************************************************************************************/
unsigned long loadLastSavedMinute() {
    SPI.begin();
    digitalWrite(CS_1, LOW);
    unsigned long v = flash.readLong(LAST_POWER_SAVE_ADDR);
    digitalWrite(CS_1, HIGH);
    SPI.end();
    Serial.println("LOAD Current Minute To Flash V:");
    Serial.println(v);
    // Convert number to string
    char msg[40];
    sprintf(msg, "LastSaved: %lu", v);

    // Send SMS to all numbers
    for (int i = 0; i < numAllowedNumbers; i++) {
        fona.sendSMS(allowedPhoneNumbers[i], msg);
    }
    return v;
}




void sendLocationToUsers() {
    float latitude, longitude;

    if (fona.GPSstatus() == 0) {
        /*for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], "GPS not locked. Try later.");
        }*/
         char smsMsg[] = "GPS not locked. Try later.";
         for (int i = 0; i < numAllowedNumbers; i++) {
         fona.sendSMS(allowedPhoneNumbers[i], smsMsg);
         }
        return;
    }

    if (fona.getGPS(&latitude, &longitude)) {
        char locationMsg[120];
        snprintf(locationMsg, sizeof(locationMsg),
                 "Click to view location: https://maps.google.com/?q=%.6f,%.6f",
                 latitude, longitude);

        for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], locationMsg);
        }
    }
    else {
        char msg14[] = "Failed to retrieve location.";
        for (int i = 0; i < numAllowedNumbers; i++) {
            fona.sendSMS(allowedPhoneNumbers[i], msg14);
        }
    }
}



void BT2()
{
  if (!isConnected && SerialBT.connected()) {
    isConnected = true;
    Serial.println("Bluetooth connected!");
    BWS = "BLUETOOTH";    // current mode you want to store
    updateBWSStatus(BWS.c_str());  // <--- STORE to flash
    linkswitches = 0;
  } else if (isConnected && !SerialBT.connected()) {
    isConnected = false;
    Serial.println("Bluetooth disconnected!");
  }

  // Check for available data
  if (SerialBT.available()) {
    String command = SerialBT.readStringUntil('\n');
    command.trim();

     BWS = "BLUETOOTH";    // current mode you want to store
    updateBWSStatus(BWS.c_str());  // <--- STORE to flash
    linkswitches = 0;
    
    // Handle single-character commands
    if (command == "INITIAL SEARCH") {
      if(isLocked == true){
        currentStatusMessageSMS = "searching.";
        SerialBT.println(String(currentStatusMessageSMS) + "|" + pump1Counter + "|" + Bpump1Counter + "|" + Cpump1Counter + "|" + switchcontrolvar + "|" + linkswitches);
        //SerialBT.print("searching.");
        }else
        {
        currentStatusMessageSMS = "Searching";
        SerialBT.println(String(currentStatusMessageSMS) + "|" + pump1Counter + "|" + Bpump1Counter + "|" + Cpump1Counter + "|" + switchcontrolvar + "|" + linkswitches);
        //SerialBT.print("Searching");
        }
    }

    else if(command == "YES")
    {
       isLocked = true;  // Lock the system
       storeLockStatus(isLocked);
       smstimer = 0;
       gpstimer = 0;
    }

    else if(command == "NO")
    {
      isLocked = false;  // Lock the system
       storeLockStatus(isLocked);
        DRIVES_STATUS = 1;
        smstimer = 1;
       gpstimer = 1;
    }

    else if(command == "UNLOCK")
    {
       isLocked = false;  // Lock the system
       storeLockStatus(isLocked);
        float currentLatitude, currentLongitude;
                if (fona.getGPS(&currentLatitude, &currentLongitude)) {
                    char fullLatitude[15];  // Buffer for full latitude
                    char fullLongitude[15]; // Buffer for full longitude

                    // No significant location change, continue normal operation
                    snprintf(fullLatitude, sizeof(fullLatitude), "%.6f", currentLatitude);
                    snprintf(fullLongitude, sizeof(fullLongitude), "%.6f", currentLongitude);
                    char locationMsg[100];
                    delay(1000);
                    snprintf(locationMsg, sizeof(locationMsg), "Click the link to view the location: https://maps.google.com/?q=%.6f,%.6f", currentLatitude, currentLongitude);

                    // Send SMS to all allowed numbers
                    for (int i = 0; i < numAllowedNumbers; i++) {
                        fona.sendSMS(allowedPhoneNumbers[i], locationMsg);
                    }

                    // Optionally update previous coordinates
                    previousLatitude = currentLatitude;
                    previousLongitude = currentLongitude;
                    storePreviousLocation(previousLatitude, previousLongitude);
                }
       DRIVES_STATUS = 1;
       loadupdatedSMSStatus();
       Previousstate();
       smstimer = 1;
       gpstimer = 1;
       signal();
    }
  }
}

