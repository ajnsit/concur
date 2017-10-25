var h$ffi =
/******/ (function(modules) { // webpackBootstrap
/******/ 	// The module cache
/******/ 	var installedModules = {};
/******/
/******/ 	// The require function
/******/ 	function __webpack_require__(moduleId) {
/******/
/******/ 		// Check if module is in cache
/******/ 		if(installedModules[moduleId]) {
/******/ 			return installedModules[moduleId].exports;
/******/ 		}
/******/ 		// Create a new module (and put it into the cache)
/******/ 		var module = installedModules[moduleId] = {
/******/ 			i: moduleId,
/******/ 			l: false,
/******/ 			exports: {}
/******/ 		};
/******/
/******/ 		// Execute the module function
/******/ 		modules[moduleId].call(module.exports, module, module.exports, __webpack_require__);
/******/
/******/ 		// Flag the module as loaded
/******/ 		module.l = true;
/******/
/******/ 		// Return the exports of the module
/******/ 		return module.exports;
/******/ 	}
/******/
/******/
/******/ 	// expose the modules object (__webpack_modules__)
/******/ 	__webpack_require__.m = modules;
/******/
/******/ 	// expose the module cache
/******/ 	__webpack_require__.c = installedModules;
/******/
/******/ 	// define getter function for harmony exports
/******/ 	__webpack_require__.d = function(exports, name, getter) {
/******/ 		if(!__webpack_require__.o(exports, name)) {
/******/ 			Object.defineProperty(exports, name, {
/******/ 				configurable: false,
/******/ 				enumerable: true,
/******/ 				get: getter
/******/ 			});
/******/ 		}
/******/ 	};
/******/
/******/ 	// getDefaultExport function for compatibility with non-harmony modules
/******/ 	__webpack_require__.n = function(module) {
/******/ 		var getter = module && module.__esModule ?
/******/ 			function getDefault() { return module['default']; } :
/******/ 			function getModuleExports() { return module; };
/******/ 		__webpack_require__.d(getter, 'a', getter);
/******/ 		return getter;
/******/ 	};
/******/
/******/ 	// Object.prototype.hasOwnProperty.call
/******/ 	__webpack_require__.o = function(object, property) { return Object.prototype.hasOwnProperty.call(object, property); };
/******/
/******/ 	// __webpack_public_path__
/******/ 	__webpack_require__.p = "";
/******/
/******/ 	// Load entry module and return exports
/******/ 	return __webpack_require__(__webpack_require__.s = 0);
/******/ })
/************************************************************************/
/******/ ([
/* 0 */
/***/ (function(module, __webpack_exports__, __webpack_require__) {

"use strict";
Object.defineProperty(__webpack_exports__, "__esModule", { value: true });
/* harmony import */ var __WEBPACK_IMPORTED_MODULE_0_react_native__ = __webpack_require__(1);
/* harmony import */ var __WEBPACK_IMPORTED_MODULE_0_react_native___default = __webpack_require__.n(__WEBPACK_IMPORTED_MODULE_0_react_native__);
/* harmony reexport (binding) */ if(__webpack_require__.o(__WEBPACK_IMPORTED_MODULE_0_react_native__, "Text")) __webpack_require__.d(__webpack_exports__, "Text", function() { return __WEBPACK_IMPORTED_MODULE_0_react_native__["Text"]; });
/* harmony reexport (binding) */ if(__webpack_require__.o(__WEBPACK_IMPORTED_MODULE_0_react_native__, "View")) __webpack_require__.d(__webpack_exports__, "View", function() { return __WEBPACK_IMPORTED_MODULE_0_react_native__["View"]; });
/* harmony reexport (binding) */ if(__webpack_require__.o(__WEBPACK_IMPORTED_MODULE_0_react_native__, "StyleSheet")) __webpack_require__.d(__webpack_exports__, "StyleSheet", function() { return __WEBPACK_IMPORTED_MODULE_0_react_native__["StyleSheet"]; });




/***/ }),
/* 1 */
/***/ (function(module, exports, __webpack_require__) {

"use strict";
/**
 * Copyright (c) 2015-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 *
 * @providesModule react-native-implementation
 * @flow
 */


const invariant = __webpack_require__(2);

// Export React, plus some native additions.
const ReactNative = {
  // Components
  get AccessibilityInfo() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"AccessibilityInfo\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get ActivityIndicator() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"ActivityIndicator\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get ART() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"ReactNativeART\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get Button() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Button\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get DatePickerIOS() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"DatePickerIOS\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get DrawerLayoutAndroid() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"DrawerLayoutAndroid\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get FlatList() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"FlatList\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get Image() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Image\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get ImageBackground() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"ImageBackground\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get ImageEditor() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"ImageEditor\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get ImageStore() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"ImageStore\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get KeyboardAvoidingView() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"KeyboardAvoidingView\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get ListView() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"ListView\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get Modal() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Modal\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get NavigatorIOS() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"NavigatorIOS\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get Picker() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Picker\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get PickerIOS() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"PickerIOS\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get ProgressBarAndroid() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"ProgressBarAndroid\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get ProgressViewIOS() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"ProgressViewIOS\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get ScrollView() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"ScrollView\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get SectionList() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"SectionList\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get SegmentedControlIOS() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"SegmentedControlIOS\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get Slider() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Slider\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get SnapshotViewIOS() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"SnapshotViewIOS\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get Switch() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Switch\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get RefreshControl() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"RefreshControl\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get StatusBar() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"StatusBar\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get SwipeableListView() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"SwipeableListView\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get TabBarIOS() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"TabBarIOS\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get Text() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Text\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get TextInput() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"TextInput\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get ToastAndroid() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"ToastAndroid\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get ToolbarAndroid() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"ToolbarAndroid\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get Touchable() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Touchable\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get TouchableHighlight() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"TouchableHighlight\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get TouchableNativeFeedback() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"TouchableNativeFeedback\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get TouchableOpacity() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"TouchableOpacity\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get TouchableWithoutFeedback() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"TouchableWithoutFeedback\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get View() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"View\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get ViewPagerAndroid() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"ViewPagerAndroid\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get VirtualizedList() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"VirtualizedList\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get WebView() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"WebView\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },

  // APIs
  get ActionSheetIOS() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"ActionSheetIOS\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get AdSupportIOS() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"AdSupportIOS\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get Alert() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Alert\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get AlertIOS() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"AlertIOS\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get Animated() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Animated\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get AppRegistry() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"AppRegistry\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get AppState() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"AppState\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get AsyncStorage() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"AsyncStorage\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get BackAndroid() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"BackAndroid\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); }, // deprecated: use BackHandler instead
  get BackHandler() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"BackHandler\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get CameraRoll() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"CameraRoll\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get Clipboard() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Clipboard\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get DatePickerAndroid() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"DatePickerAndroid\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get DeviceInfo() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"DeviceInfo\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get Dimensions() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Dimensions\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get Easing() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Easing\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get findNodeHandle() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"ReactNative\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())).findNodeHandle; },
  get I18nManager() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"I18nManager\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get ImagePickerIOS() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"ImagePickerIOS\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get InteractionManager() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"InteractionManager\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get Keyboard() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Keyboard\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get LayoutAnimation() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"LayoutAnimation\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get Linking() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Linking\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get NativeEventEmitter() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"NativeEventEmitter\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get NetInfo() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"NetInfo\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get PanResponder() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"PanResponder\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get PermissionsAndroid() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"PermissionsAndroid\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get PixelRatio() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"PixelRatio\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get PushNotificationIOS() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"PushNotificationIOS\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get Settings() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Settings\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get Share() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Share\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get StatusBarIOS() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"StatusBarIOS\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get StyleSheet() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"StyleSheet\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get Systrace() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Systrace\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get TimePickerAndroid() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"TimePickerAndroid\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get TVEventHandler() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"TVEventHandler\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get UIManager() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"UIManager\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get unstable_batchedUpdates() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"ReactNative\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())).unstable_batchedUpdates; },
  get Vibration() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Vibration\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get VibrationIOS() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"VibrationIOS\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },

  // Plugins
  get DeviceEventEmitter() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"RCTDeviceEventEmitter\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get NativeAppEventEmitter() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"RCTNativeAppEventEmitter\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get NativeModules() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"NativeModules\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get Platform() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"Platform\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get processColor() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"processColor\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get requireNativeComponent() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"requireNativeComponent\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get takeSnapshot() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"takeSnapshot\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },

  // Prop Types
  get ColorPropType() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"ColorPropType\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get EdgeInsetsPropType() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"EdgeInsetsPropType\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get PointPropType() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"PointPropType\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },
  get ViewPropTypes() { return __webpack_require__(!(function webpackMissingModule() { var e = new Error("Cannot find module \"ViewPropTypes\""); e.code = 'MODULE_NOT_FOUND'; throw e; }())); },

  // Deprecated
  get Navigator() {
    invariant(
      false,
      'Navigator is deprecated and has been removed from this package. It can now be installed ' +
      'and imported from `react-native-deprecated-custom-components` instead of `react-native`. ' +
      'Learn about alternative navigation solutions at http://facebook.github.io/react-native/docs/navigation.html'
    );
  },
};

module.exports = ReactNative;


/***/ }),
/* 2 */
/***/ (function(module, exports, __webpack_require__) {

"use strict";
/* WEBPACK VAR INJECTION */(function(process) {/**
 * Copyright (c) 2013-present, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 *
 */



/**
 * Use invariant() to assert state which your program assumes to be true.
 *
 * Provide sprintf-style format (only %s is supported) and arguments
 * to provide information about what broke and what you were
 * expecting.
 *
 * The invariant message will be stripped in production, but the invariant
 * will remain to ensure logic does not differ in production.
 */

var validateFormat = function validateFormat(format) {};

if (process.env.NODE_ENV !== 'production') {
  validateFormat = function validateFormat(format) {
    if (format === undefined) {
      throw new Error('invariant requires an error message argument');
    }
  };
}

function invariant(condition, format, a, b, c, d, e, f) {
  validateFormat(format);

  if (!condition) {
    var error;
    if (format === undefined) {
      error = new Error('Minified exception occurred; use the non-minified dev environment ' + 'for the full error message and additional helpful warnings.');
    } else {
      var args = [a, b, c, d, e, f];
      var argIndex = 0;
      error = new Error(format.replace(/%s/g, function () {
        return args[argIndex++];
      }));
      error.name = 'Invariant Violation';
    }

    error.framesToPop = 1; // we don't care about invariant's own frame
    throw error;
  }
}

module.exports = invariant;
/* WEBPACK VAR INJECTION */}.call(exports, __webpack_require__(3)))

/***/ }),
/* 3 */
/***/ (function(module, exports) {

// shim for using process in browser
var process = module.exports = {};

// cached from whatever global is present so that test runners that stub it
// don't break things.  But we need to wrap it in a try catch in case it is
// wrapped in strict mode code which doesn't define any globals.  It's inside a
// function because try/catches deoptimize in certain engines.

var cachedSetTimeout;
var cachedClearTimeout;

function defaultSetTimout() {
    throw new Error('setTimeout has not been defined');
}
function defaultClearTimeout () {
    throw new Error('clearTimeout has not been defined');
}
(function () {
    try {
        if (typeof setTimeout === 'function') {
            cachedSetTimeout = setTimeout;
        } else {
            cachedSetTimeout = defaultSetTimout;
        }
    } catch (e) {
        cachedSetTimeout = defaultSetTimout;
    }
    try {
        if (typeof clearTimeout === 'function') {
            cachedClearTimeout = clearTimeout;
        } else {
            cachedClearTimeout = defaultClearTimeout;
        }
    } catch (e) {
        cachedClearTimeout = defaultClearTimeout;
    }
} ())
function runTimeout(fun) {
    if (cachedSetTimeout === setTimeout) {
        //normal enviroments in sane situations
        return setTimeout(fun, 0);
    }
    // if setTimeout wasn't available but was latter defined
    if ((cachedSetTimeout === defaultSetTimout || !cachedSetTimeout) && setTimeout) {
        cachedSetTimeout = setTimeout;
        return setTimeout(fun, 0);
    }
    try {
        // when when somebody has screwed with setTimeout but no I.E. maddness
        return cachedSetTimeout(fun, 0);
    } catch(e){
        try {
            // When we are in I.E. but the script has been evaled so I.E. doesn't trust the global object when called normally
            return cachedSetTimeout.call(null, fun, 0);
        } catch(e){
            // same as above but when it's a version of I.E. that must have the global object for 'this', hopfully our context correct otherwise it will throw a global error
            return cachedSetTimeout.call(this, fun, 0);
        }
    }


}
function runClearTimeout(marker) {
    if (cachedClearTimeout === clearTimeout) {
        //normal enviroments in sane situations
        return clearTimeout(marker);
    }
    // if clearTimeout wasn't available but was latter defined
    if ((cachedClearTimeout === defaultClearTimeout || !cachedClearTimeout) && clearTimeout) {
        cachedClearTimeout = clearTimeout;
        return clearTimeout(marker);
    }
    try {
        // when when somebody has screwed with setTimeout but no I.E. maddness
        return cachedClearTimeout(marker);
    } catch (e){
        try {
            // When we are in I.E. but the script has been evaled so I.E. doesn't  trust the global object when called normally
            return cachedClearTimeout.call(null, marker);
        } catch (e){
            // same as above but when it's a version of I.E. that must have the global object for 'this', hopfully our context correct otherwise it will throw a global error.
            // Some versions of I.E. have different rules for clearTimeout vs setTimeout
            return cachedClearTimeout.call(this, marker);
        }
    }



}
var queue = [];
var draining = false;
var currentQueue;
var queueIndex = -1;

function cleanUpNextTick() {
    if (!draining || !currentQueue) {
        return;
    }
    draining = false;
    if (currentQueue.length) {
        queue = currentQueue.concat(queue);
    } else {
        queueIndex = -1;
    }
    if (queue.length) {
        drainQueue();
    }
}

function drainQueue() {
    if (draining) {
        return;
    }
    var timeout = runTimeout(cleanUpNextTick);
    draining = true;

    var len = queue.length;
    while(len) {
        currentQueue = queue;
        queue = [];
        while (++queueIndex < len) {
            if (currentQueue) {
                currentQueue[queueIndex].run();
            }
        }
        queueIndex = -1;
        len = queue.length;
    }
    currentQueue = null;
    draining = false;
    runClearTimeout(timeout);
}

process.nextTick = function (fun) {
    var args = new Array(arguments.length - 1);
    if (arguments.length > 1) {
        for (var i = 1; i < arguments.length; i++) {
            args[i - 1] = arguments[i];
        }
    }
    queue.push(new Item(fun, args));
    if (queue.length === 1 && !draining) {
        runTimeout(drainQueue);
    }
};

// v8 likes predictible objects
function Item(fun, array) {
    this.fun = fun;
    this.array = array;
}
Item.prototype.run = function () {
    this.fun.apply(null, this.array);
};
process.title = 'browser';
process.browser = true;
process.env = {};
process.argv = [];
process.version = ''; // empty string to avoid regexp issues
process.versions = {};

function noop() {}

process.on = noop;
process.addListener = noop;
process.once = noop;
process.off = noop;
process.removeListener = noop;
process.removeAllListeners = noop;
process.emit = noop;
process.prependListener = noop;
process.prependOnceListener = noop;

process.listeners = function (name) { return [] }

process.binding = function (name) {
    throw new Error('process.binding is not supported');
};

process.cwd = function () { return '/' };
process.chdir = function (dir) {
    throw new Error('process.chdir is not supported');
};
process.umask = function() { return 0; };


/***/ })
/******/ ]);