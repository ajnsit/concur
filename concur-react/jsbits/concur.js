global.h$concur = {
    React: require('react'),
    ReactDOM: require('react-dom'),
    makeHandler: function(action, async) {
      var f = function(ev) {
        return h$concurEventCallback(async, action, ev);
      };
      // TODO: Handle cleanup
      f.hsAction = action;
      return f;
    }
};
