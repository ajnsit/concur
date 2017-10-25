import React from 'react';
import { Concur } from '.jsbits/index.compiled';

export default class App extends React.Component {
  constructor(props) {
    super(props);
    this.state = {render: Concur.initView(this)};
  }
  render() {
    return this.state.render();
  }
}
