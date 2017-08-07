// A Functional Way to write React

var mkState = function(countNow, self) {
  // react only does shallow state comparisons, so putting a function in is okay
  return {render: view(countNow, mkClickHandler(countNow, self))};
};

var mkClickHandler = function(countNow, self) {
  return function() {
    self.setState(mkState(countNow+1, self));
  };
};

var view = function (count, handleClick) {
  return function() { return (
    <div>
      <div>Your click count is {count}.</div>
      <div><button onClick={handleClick}>Count up</button></div>
    </div>
  );};
};

var initialCount = 0;

var Count = React.createClass({
  getInitialState: function() {
    return mkState(initialCount, this);
  },
  render: function() {
    return this.state.render();
  }
});

React.render(<Count />, document.getElementById("count"));
